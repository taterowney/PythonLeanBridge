import shutil
import multiprocessing
import requests
from urllib.parse import quote
from typing import Iterator, Optional, Pattern, Sequence, Mapping, Tuple
import subprocess, json
from pathlib import Path


def stream_lean_command(command, project_dir: str | Path = Path.cwd()):
    """
    Run a Lean command asynchronously and return the output.
    """
    command = ["lake", "exe"] + command.split(" ")

    with subprocess.Popen(
        command,
        cwd=project_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,              # text mode (same as universal_newlines=True)
        encoding="utf-8",
        errors="replace",
        bufsize=1,
    ) as proc:
        assert proc.stdout is not None  # for type checkers
        # Yield lines as they arrive; '' indicates EOF.
        for line in iter(proc.stdout.readline, ""):
            yield line.rstrip("\n")

        # Ensure process has exited; raise if requested and non-zero.
        returncode = proc.wait()
        if returncode != 0:
            raise subprocess.CalledProcessError(returncode, cmd=command)

class LeanEnvironment:
    def __init__(self, modules: list['Module']):
        self.modules = modules
        assert len(modules) > 0
        self.lean_dir = modules[0].lean_dir
        self.process = None

    def open(self):
        self.process = subprocess.Popen(
            ["lake", "exe", "bridge_python_to_lean", ",".join([m.name for m in self.modules])],
            cwd=self.lean_dir,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            encoding="utf-8",
            errors="replace",
            bufsize=1
        )
        return self

    def close(self):
        if self.process:
            self.process.terminate()
            self.process.wait()
            self.process = None

    def __enter__(self):
        return self.open()

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def send_and_stream(self, command: str):
        if not self.process:
            raise RuntimeError("REPL process is not running. Use __enter__ to start it.")

        self.process.stdin.write(command + "\n")
        self.process.stdin.flush()

        # Stream the output
        for line in iter(self.process.stdout.readline, b""):
            self.process.stdout.flush()
            # print(self.process.poll())
            if not line:
                continue
            if line.startswith("2131792754394826543"):
                break
            yield line.rstrip("\n")

    def run_command(self, name, arg):
        result = list(self.send_and_stream(json.dumps({"name": name, "arg": arg})))
        if len(result) == 0:
            raise RuntimeError(f"Command {name} returned no output. Lean may have crashed. ")
        final = json.loads(result[-1].rstrip("\n"))
        if final["type"] == "Error":
            raise RuntimeError(f"Command {name} failed with error: {final['message']}")
        elif final["type"] == "String":
            return final["value"]
        elif final["type"] == "Nat":
            return int(final["value"])
        elif final["type"] == "Bool":
            return final["value"] == "true"
        elif final["type"] == "Lean.Json":
            return json.loads(final["value"])
        else:
            raise RuntimeError(f"Command {name} returned unexpected type: {final['type']}")

    def stream_output(self, name, arg):
        last = ""
        for value in self.send_and_stream(json.dumps({"name": name, "arg": arg, "printResult": True})):
            if last:
                yield last
            last = value
        try:
            final = json.loads(last.rstrip("\n"))
            if final["type"] == "Error":
                raise RuntimeError(f"Command {name} failed with error: {final['value']}")
        except json.JSONDecodeError:
            raise RuntimeError(f"Command {name} appears to have stopped unexpectedly. Last output: {last}")



def run_lean_command(command, project_dir: str | Path = Path.cwd()):
    """
    Run a Lean command synchronously and return the output.
    """
    return list(stream_lean_command(command, project_dir))


def check_leanRAG_installation(
    project_dir: str | Path = Path.cwd(),
) -> None:
    return
    """
    Ensure that the LeanRAG package is listed in the project's Lake
    configuration and built.  *project_dir* must point at the root of a
    Lean-4 workspace (i.e. containing `lakefile.toml` or `lakefile.lean`).

    Parameters
    ----------
    project_dir : str | Path, default = current working directory
        Path to the Lean workspace root.

    Raises
    ------
    FileNotFoundError
        If neither a `lakefile.toml` nor a `lakefile.lean` exists.
    EnvironmentError
        If `lake` is not on the user’s PATH.
    RuntimeError
        If one of the `lake` commands fails.
    """
    project_dir = Path(project_dir).resolve()

    # ------------------------------------------------------------------
    # 1.  Fast path – already listed in *lake-manifest.json*?
    # ------------------------------------------------------------------
    manifest = project_dir / "lake-manifest.json"
    if manifest.is_file():
        with manifest.open(encoding="utf-8") as f:
            data = json.load(f)
        if (
            data.get("name") == "LeanRAG"
            or any(pkg.get("name") == "LeanRAG" for pkg in data.get("packages", []))
        ):
            return  # everything in place — nothing to do.

    # ------------------------------------------------------------------
    # 2.  Patch the Lake configuration (TOML or Lean DSL).
    # ------------------------------------------------------------------
    toml_file = project_dir / "lakefile.toml"
    lean_file = project_dir / "lakefile.lean"

    git_url = "https://github.com/taterowney/LeanRAG"
    if (project_dir / "lean-toolchain").exists():
        with open(project_dir / "lean-toolchain", "r") as f:
            lean_version = f.read().strip().replace("leanprover/lean4:v", "")
    else:
        raise FileNotFoundError(
            f"lean-toolchain file not found in {project_dir}. Directory might not be a Lean project."
        )

    try:
        rev = get_leanrag_branch_commit(lean_version, repo="taterowney/LeanRAG")[1]
        # rev = get_leanrag_tag_commit("lean-v" + lean_version, repo="taterowney/LeanRAG")[1]
    except ValueError:
        raise ValueError(
            f"Detected Lean version {lean_version} is not currently supported by LeanRAG. "
        )

    # if not input("It looks like LeanRAG is not installed and/or built in your Lean project. Would you like to add it? (y/N) ").strip().lower().startswith("y"):
    #     return
    print("LeanRAG not found in the project. Adding it and rebuilding...")

    if toml_file.exists():
        text = toml_file.read_text(encoding="utf-8")
        if 'name = "LeanRAG"' not in text:
            snippet = (
                "\n[[require]]\n"
                f'name = "LeanRAG"\n'
                f'git  = "{git_url}"\n'
                f'rev  = "{lean_version}"\n'
            )
            toml_file.write_text(text + snippet, encoding="utf-8")

    elif lean_file.exists():
        text = lean_file.read_text(encoding="utf-8")
        if "require" not in text or "LeanRAG" not in text:
            snippet = (
                f'\nrequire LeanRAG from git "{git_url}" @ "{lean_version}"\n'
            )
            # Insert after the last existing `require` (or at EOF).
            insert_at = text.rfind("require ") #TODO: make sure it's not in a comment
            if insert_at == -1:
                lean_file.write_text(text + snippet, encoding="utf-8")
            else:
                head, tail = text[: insert_at].rstrip(), text[insert_at:]
                lean_file.write_text(f"{head}\n{snippet}{tail}", encoding="utf-8")
    else:
        raise FileNotFoundError(
            f"Neither lakefile.toml nor lakefile.lean found in {project_dir}"
        )
    # ------------------------------------------------------------------
    # 2.5 (I forgor).   Patch the lake-manifest file directly so we don't have to regenerate it to avoid problems with outdated repository versions.
    # ------------------------------------------------------------------
    if manifest.is_file():
        with manifest.open(encoding="utf-8") as f:
            data = json.load(f)
        if "packages" not in data:
            data["packages"] = []
        if not any(pkg.get("name") == "LeanRAG" for pkg in data["packages"]):
            data["packages"].append({"url": "https://github.com/taterowney/LeanRAG",
               "type": "git",
               "subDir": None,
               "scope": "",
               "rev": rev,
               "name": "LeanRAG",
               "manifestFile": "lake-manifest.json",
               "inputRev": rev,
               "inherited": False,
               "configFile": "lakefile.toml"})
        with manifest.open("w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)

    # ------------------------------------------------------------------
    # 3.  Use Lake to rebuild project dependencies.
    # ------------------------------------------------------------------
    if shutil.which("lake") is None:
        raise EnvironmentError(
            "The `lake` tool cannot be found on your PATH; "
            "please install the Lean toolchain first."
        )

    try:
        subprocess.run(
            ["lake", "build", "LeanRAG"],
            cwd=project_dir,
            check=True,
            text=True,
        )
    except subprocess.CalledProcessError as exc:
        print("Quick rebuild failed. Erasing and rebuilding your .lake directory (this may take a minute)...")
        try:
            shutil.rmtree(project_dir / ".lake")

            subprocess.run(
                ["lake", "exe", "cache", "get"],
                cwd=project_dir,
                check=False,
                text=True,
            )
            subprocess.run(
                ["lake", "build"],
                cwd=project_dir,
                check=True,
                text=True,
            )
            subprocess.run(
                ["lake", "build", "LeanRAG"],
                cwd=project_dir,
                check=True,
                text=True,
            )
        except subprocess.CalledProcessError as exc:
            raise RuntimeError(exc.stderr or str(exc)) from exc

def get_leanrag_branch_commit(
    branch: str,
    *,
    repo: str = "taterowney/LeanRAG",
    token: Optional[str] = None,
    timeout: float = 10.0,
) -> Tuple[str, str]:
    """
    Return ``(branch_name, commit_sha)`` for *branch* in *repo*.

    Parameters
    ----------
    branch : str
        The branch name exactly as it appears on GitHub
        (e.g. "main", "develop", "feature/x").
    repo : str, default = "taterowney/LeanRAG"
        Repository in the form ``owner/repo``.
    token : str | None
        Personal-access token (optional but recommended to avoid low
        anonymous rate-limits or when the repo is private).
    timeout : float, default = 10 s
        Network timeout (seconds) for the HTTP request.

    Returns
    -------
    (branch_name, commit_sha) : tuple[str, str]

    Raises
    ------
    ValueError
        If the branch does not exist.
    requests.HTTPError
        For other, non-200 HTTP responses.
    """
    owner, repo_name = repo.split("/", 1)
    # The branch segment must be URL-encoded so "feature/x" works:
    endpoint = (
        f"https://api.github.com/repos/{owner}/{repo_name}/branches/{quote(branch, safe='')}"
    )

    headers = {"Accept": "application/vnd.github+json"}
    if token:
        headers["Authorization"] = f"Bearer {token.strip()}"

    resp = requests.get(endpoint, headers=headers, timeout=timeout)

    if resp.status_code == 404:
        raise ValueError(f"Branch {branch!r} not found in {repo!r}")
    resp.raise_for_status()

    data = resp.json()
    return data["name"], data["commit"]["sha"]


def get_leanrag_tag_commit(
    version: str,
    *,
    repo: str = "taterowney/LeanRAG",
    token: Optional[str] = None,
    timeout: float = 10.0,
) -> Tuple[str, str]:
    """
    Look up a Git tag in the ``taterowney/LeanRAG`` repository and return
    ``(tag_name, commit_sha)``.

    Parameters
    ----------
    version : str
        The version string to match, e.g. ``"1.4.0"`` or ``"v1.4.0"``.
    repo : str, default = "taterowney/LeanRAG"
        The GitHub repository in ``owner/repo`` format.
    token : str | None
        Optional GitHub personal-access token. Provide one to increase the
        rate-limit quota or when accessing a private fork.
    timeout : float, default = 10.0
        Seconds to wait for each network request.

    Returns
    -------
    (tag_name, commit_sha) : tuple[str, str]

    Raises
    ------
    ValueError
        If no matching tag is found.
    requests.HTTPError
        For non-200 responses.
    """
    owner, repo_name = repo.split("/", 1)
    base = f"https://api.github.com/repos/{owner}/{repo_name}"
    url = f"{base}/git/refs/tags"        # official endpoint for listing tags

    headers = {"Accept": "application/vnd.github+json"}
    if token:
        headers["Authorization"] = f"Bearer {token.strip()}"

    # Normalise the version so both “1.4.0” and “v1.4.0” will match.
    wanted = version.lstrip("v")

    while url:
        r = requests.get(url, headers=headers, timeout=timeout, params={"per_page": 100})
        r.raise_for_status()
        for ref in r.json():
            tag_name = ref["ref"].split("/", 2)[-1]      # "refs/tags/v1.4.0" -> "v1.4.0"
            if tag_name.lstrip("v") == wanted:
                return tag_name, ref["object"]["sha"]

        # follow pagination if a “next” link is present
        url = None
        if link := r.headers.get("Link"):
            for part in link.split(","):
                segment, rel = part.split(";", 1)
                if 'rel="next"' in rel:
                    url = segment.strip(" <>")
                    break

    raise ValueError(f"No tag matching version '{version}' found in {repo!r}")

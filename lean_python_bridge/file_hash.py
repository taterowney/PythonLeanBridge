from pathlib import Path
from typing import Sequence, Union
import os, struct

# Try BLAKE3 (very fast). Fallback to hashlib.sha256.
try:
    import blake3  # pip install blake3
    _HAS_BLAKE3 = True
except Exception:
    _HAS_BLAKE3 = False
    import hashlib


def _file_hash_and_size(p: Path, chunk_bytes: int = 4 * 1024 * 1024):
    """Return (digest_bytes, size) for a single file by streaming its bytes."""
    h = blake3.blake3() if _HAS_BLAKE3 else hashlib.sha256()
    size = 0
    with p.open("rb", buffering=0) as f:
        for chunk in iter(lambda: f.read(chunk_bytes), b""):
            h.update(chunk)
            size += len(chunk)
    return h.digest(), size


def hash_files(
    paths: Sequence[Union[str, Path]],
    parent_dir: Union[str, Path],
    *,
    algo: str = "blake3",            # "blake3" or "sha256"
    order: str = "by_relpath",       # "by_relpath" (default), "by_content", or "by_input"
    chunk_bytes: int = 4 * 1024 * 1024,
) -> str:
    """
    Compute a single digest over many files, based on their *contents and relative paths*.
    - parent_dir: paths are hashed relative to this directory (POSIX-style separators).
    - order="by_relpath" (default) ignores input ordering and sorts by normalized relative path.
      "by_content" sorts by per-file (content digest, size, then path),
      "by_input" preserves the given order.

    Returns a hex digest string.
    """
    parent = Path(parent_dir).resolve()
    files = [Path(p).resolve() for p in paths]

    # Validate files
    for p in files:
        if not p.is_file():
            raise FileNotFoundError(f"Not a file: {p}")

    # Outer hasher
    use_blake3 = _HAS_BLAKE3 and algo.lower() == "blake3"
    outer = blake3.blake3() if use_blake3 else hashlib.sha256()

    # Build (relpath_bytes, digest, size) for each file
    per_file = []
    for p in files:
        # Relativize to parent; normalize to POSIX separators for cross-platform stability
        rel = os.path.relpath(p, parent).replace(os.sep, "/")
        rel_b = rel.encode("utf-8")

        digest, size = _file_hash_and_size(p, chunk_bytes)
        per_file.append((rel_b, digest, size))

    # Decide combination order (keeps result independent of input list order unless by_input)
    if order == "by_relpath":
        per_file.sort(key=lambda t: t[0])                 # sort by relative path
    elif order == "by_content":
        per_file.sort(key=lambda t: (t[1], t[2], t[0]))   # digest, size, then path
    elif order == "by_input":
        pass
    else:
        raise ValueError('order must be "by_relpath", "by_content", or "by_input"')

    # Combine: for each file, feed (len(path), path bytes, content digest, size) into the outer hasher
    for rel_b, digest, size in per_file:
        outer.update(struct.pack("<I", len(rel_b)))  # 4-byte length of path
        outer.update(rel_b)                          # path bytes
        outer.update(digest)                         # content digest
        outer.update(struct.pack("<Q", size))        # 8-byte file size

    return outer.hexdigest()
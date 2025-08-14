from pathlib import Path
import json, warnings, subprocess
import duckdb
from typing import Union, Sequence, Mapping, Iterable, Any
import shutil

from .bridge_python_to_lean import check_leanRAG_installation, LeanEnvironment
from .file_hash import hash_files


SEARCH_PATH_ENTRIES = [
    ".",
    ".lake/packages/*/",
    ".elan/toolchains/leanprover--lean4---v{}/src/lean/"
]

class Module:
    def __init__(self, name, lean_dir=Path.cwd()):
        if type(lean_dir) is str:
            lean_dir = Path(lean_dir)
        self.lean_dir = lean_dir.resolve()
        if not ((self.lean_dir / "lakefile.toml").exists() or (self.lean_dir / "lakefile.lean").exists()):
            raise ValueError(f"No lakefile found in the directory {lean_dir}. Are you sure this is a Lean project?")

        self.is_file = False
        self.is_dir = False
        _module_path = Path(name)
        if _module_path.exists():
            # It's a path
            if _module_path.suffix == ".lean":
                self.is_file = True
                self.file_path = _module_path
                if Path(_module_path.as_posix().replace(".lean", "")).exists():
                    self.is_dir = True
                    self.dir_path = Path(_module_path.as_posix().replace(".lean", ""))
            elif _module_path.is_dir():
                self.is_dir = True
                self.dir_path = _module_path
                if Path(_module_path.as_posix() + ".lean").exists():
                    self.is_file = True
                    self.file_path = Path(_module_path.as_posix() + ".lean")
            rel_path = _module_path.relative_to(self.lean_dir).as_posix()
            if rel_path.startswith(".lake"):
                rel_path = "/".join(rel_path.split("/")[3:])
            self.name = rel_path.replace(".lean", "").replace("/", ".")
            self.module_identifiers = self.name.split(".")
        else:
            # It's a Lean module identifier
            self.name = name
            self.module_identifiers = self.name.split(".")

            with open(self.lean_dir / "lean-toolchain", "r") as f:
                version = f.read().strip().split(":v")[-1]
            elan_path = Path(shutil.which("lean").split(".elan/bin/lean")[0]).resolve()

            for entry in SEARCH_PATH_ENTRIES:
                if entry == ".":
                    if (self.lean_dir / ("/".join(self.module_identifiers) + ".lean")).exists():
                        self.is_file = True
                        self.file_path = self.lean_dir / ("/".join(self.module_identifiers) + ".lean")
                    if (self.lean_dir / "/".join(self.module_identifiers)).exists():
                        self.is_dir = True
                        self.dir_path = self.lean_dir / ("/".join(self.module_identifiers))
                    if self.is_file or self.is_dir:
                        break
                else:
                    if entry.startswith(".elan"):
                        entry = entry.format(version)
                        if not elan_path.exists():
                            continue
                        top_dir = elan_path
                    else:
                        top_dir = self.lean_dir

                    for d in top_dir.glob(entry):
                        if (d / ("/".join(self.module_identifiers) + ".lean")).exists():
                            self.is_file = True
                            self.file_path = d / ("/".join(self.module_identifiers) + ".lean")
                        if (d / "/".join(self.module_identifiers)).exists():

                            self.is_dir = True
                            self.dir_path = d / ("/".join(self.module_identifiers))
                        if self.is_file or self.is_dir:
                            break

        if not self.is_file and not self.is_dir:
            raise ModuleNotFoundError(f"Module {self.name} not found in {self.lean_dir}.")

        # By default, make the module a part of a "dataset" that just contains everything in the project with no constraints
        key = self.lean_dir.as_posix()
        if key not in _UNIVERSAL_ACCEPTOR_DATASET_MAP:
            _UNIVERSAL_ACCEPTOR_DATASET_MAP[key] = _UniversalAcceptorDataset(self.lean_dir)
        self.dataset = _UNIVERSAL_ACCEPTOR_DATASET_MAP[key]

        self._decls_cache = None

        self.environment = LeanEnvironment([self])

    def _check_install(self):
        self.dataset._check_install()

    def run_command(self, function_name: str, arg: str):
        """
        Run a function in the Lean environment associated with this module.
        """
        self._check_install()
        with self.environment as env:
            return env.run_command(function_name, arg)

    def stream_command_output(self, function_name: str, arg: str):
        """
        Stream the output of a function in the Lean environment associated with this module.
        """
        self._check_install()
        with self.environment as env:
            yield from env.stream_output(function_name, arg)

    def get_raw(self):
        if not self.is_file:
            raise ValueError
        with open(self.file_path, "r") as f:
            return f.read()

    def path(self):
        if self.is_file:
            return self.file_path
        return self.dir_path

    def rel_path(self):
        if self.is_file:
            return "/".join(self.module_identifiers) + ".lean"
        return "/".join(self.module_identifiers)

    def get_children(self):
        if not self.is_dir:
            return []
        ret = []
        for file in self.dir_path.iterdir():
            ret.append(Module(f"{".".join(self.module_identifiers)}.{file.as_posix().replace(".lean", "").split("/")[-1]}", lean_dir=self.lean_dir))
        return ret

    def get_parent(self):
        if len(self.module_identifiers) == 1:
            raise ModuleNotFoundError("Top-level module")
        parent_name = ".".join(self.module_identifiers[:-1])
        return Module(parent_name, lean_dir=self.lean_dir)

    def get_all_files(self):
        if not self.is_dir:
            return [self]
        ret = []
        if self.is_file:
            ret.append(self)
        for file in self.dir_path.rglob("*.lean"):
            if file.as_posix().endswith(".lean"):
                # if not ignore_blacklist and self.module_identifiers[0] == "Mathlib" and any(f"Mathlib/{x}" in file.as_posix() for x in ["Condensed", "Control", "Deprecated", "Lean", "Mathport", "Std", "Tactic", "Testing", "Util"]):
                #     continue
                ret.append(Module(
                    ".".join(self.module_identifiers) + "." + file.relative_to(self.dir_path).as_posix().replace(".lean", "").replace("/", "."),
                    lean_dir=self.lean_dir)
                )
        return ret

    def get_relevant_files(self):
        """current module + imports"""
        if not self.is_file:
            return [self]
        ret = [self]
        for line in self.get_raw().split("\n"):
            if line.startswith("import "):
                ret.extend(Module(line.split("import ")[1].strip(), lean_dir=self.lean_dir).get_relevant_files())
        return ret

    def get_declarations(self):
        return list(BatchedRetriever.get_module_declarations(self))

    def build(self):
        """
        Build the module in the Lean environment.
        """
        if self.module_identifiers[0] in ["Lean", "Init", "Std"]:
            # These are part of the standard library, so must already be built
            return
        try:
            subprocess.run(
                ["lake", "build", self.name],
                cwd=self.lean_dir,
                capture_output=True,
                text=True,
                check=True
            )
        except subprocess.CalledProcessError:
            raise RuntimeError(f"Build failed for module {self.name} in {self.lean_dir}.")

    def __getitem__(self, item):
        if type(item) != str:
            raise TypeError
        if not self.is_dir:
            raise ModuleNotFoundError
        for file in self.dir_path.iterdir():
            if file.as_posix().replace(".lean", "").endswith(item.replace("/", "")):
                return Module(f"{".".join(self.module_identifiers)}.{item}", lean_dir=self.lean_dir)
        raise ModuleNotFoundError

    def __str__(self):
        return ".".join(self.module_identifiers)

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return self.lean_dir == other.lean_dir and self.name == other.name

    def __getattr__(self, item):
        assert item != "dataset", "This module isn't part of a dataset for some reason."
        return self[item]


class Dataset:
    def __init__(self, modules : list['Module'] | list[str], name="", lean_dir=Path.cwd()):
        self.name = name

        if len(modules) == 0:
            module_names = []
        else:
            if isinstance(modules[0], str):
                module_names = modules.copy()
                modules = [Module(m, lean_dir=lean_dir) for m in modules]
            elif isinstance(modules[0], Module):
                module_names = [m.name for m in modules]
                lean_dir = modules[0].lean_dir
                if not all([m.lean_dir == lean_dir for m in modules]):
                    raise TypeError("Modules in a dataset must all belong to the same Lean project")
            else:
                raise TypeError('"modules" parameter must be a list of either strings or Modules')

        self._has_checked_install = False
        self._has_indexed_decls = False
        if isinstance(lean_dir, str):
            lean_dir = Path(lean_dir)
        self.lean_dir = lean_dir.resolve()

        self.modules = []
        for m in modules:
            if m.is_file:
                self.modules.append(m)
            else:
                self.modules.extend(m.get_all_files())
        for m in self.modules:
            m.dataset = self

        module_names.sort()

        self.uuid = hash_files([m.file_path for m in self.modules], parent_dir=self.lean_dir) # Incorporates both file content and relative paths; if these are changed, then the dataset will recompute itself



    def _maybe_index_decls(self):
        if not self._has_indexed_decls:
            BatchedRetriever.register_dataset(self)
            self._has_indexed_decls = True

    def _check_install(self):
        if not self._has_checked_install:
            check_leanRAG_installation(project_dir=self.lean_dir)
            for m in self.modules:
                m.build()  # Since we get most data directly from cached oleans, we make sure they're all built before we start
        self._has_checked_install = True

    def _retrieve_all_declarations(self):
        # yield from [["LeanRAG.Basic", "test", "kind", "text", '[{"name": "test2", "module": "LeanRAG.Basic"}]', "type", "initialProofState", True], ["LeanRAG.Basic", "test2", "kind", "text", "[]", "type", "initialProofState", True]]
        self._check_install()
        if len(self.modules) > 0:
            with LeanEnvironment([Module("LeanRAG.FastDeclarationsInfo", lean_dir=self.lean_dir)]) as env:
                for line in env.stream_output("get_decls", ",".join([m.name for m in self.modules])):
                    data = json.loads(line)
                    yield data["module"], data["name"], data["kind"], data["text"], str(data["dependencies"]).replace("'", '"'), data["type"], data["initialProofState"], data["module"] in [m.name for m in self.modules]

    def get_declaration_from_identifiers(self, module: Module, decl_name: str):
        """
        Get a declaration by its module and name.
        """
        return BatchedRetriever.get_declaration(module, decl_name)

    def get_declarations(self):
        """
        Get all declarations in the dataset.
        """
        self._maybe_index_decls()
        return BatchedRetriever.get_dataset_declarations(self)

    def add_dependencies(self, iterations=1):
        """
        Add dependencies to the dataset by iterating over the declarations and their dependencies.
        """
        assert iterations >= 1
        new_ds = self
        for i in range(iterations):
            mods = new_ds.modules.copy()
            has_added = False
            for s in BatchedRetriever.fetch_all_dependency_strings(new_ds):
                data = json.loads(s)
                for dep in data:
                    try:
                        mod = Module(dep["module"], lean_dir=new_ds.lean_dir)
                        if mod not in new_ds.modules:
                            mods.append(mod)
                            has_added = True
                    except ModuleNotFoundError:
                        pass
            new_ds = Dataset(mods, name=self.name + f" with level-{iterations} dependencies", lean_dir=self.lean_dir)
            if not has_added:
                break
        return new_ds

class _UniversalAcceptorDataset(Dataset):
    def __init__(self, lean_dir):
        super().__init__([], name=f"Lean project at {lean_dir}", lean_dir=lean_dir)

_UNIVERSAL_ACCEPTOR_DATASET_MAP = {}



Row = Union[Sequence[Any], Mapping[str, Any]]

class BatchedRetriever:
    """
    Turns functions that extract information from Dataset objects into a retriever that yields the same information given a module and a declaration name (via caching).

    Example usage:
    ```
    @BatchedRetriever("attribute1", "attribute2")
    def get_info(ds: Dataset) -> Iterable[Dict[str, str]]:
        yield {"attribute1": "value1", "attribute2": "value2", ...}

    print(get_info(module, "declaration_name", "attribute1"))
    ```

    Parameters
    ----------
    operation : callable
    """
    con = duckdb.connect(".db/cache.duckdb")
    table_initialized = False
    attrs_map = {}

    @classmethod
    def initialize_table(cls):
        if not cls.table_initialized:
            cls.con.execute(
                f"""
                CREATE TABLE IF NOT EXISTS declaration_data (
                    module TEXT,
                    name   TEXT,
                    kind   TEXT,
                    text   TEXT,
                    dependencies      TEXT,
                    type   TEXT,
                    initialProofState TEXT,
                    PRIMARY KEY (module, name)
                )
                """
            )
        cls.table_initialized = True


    @classmethod
    def register_dataset(cls, ds : Dataset):
        cls.initialize_table()
        if "dataset_" + ds.uuid not in cls.con.table("declaration_data").columns:
            print(f"Indexing declarations for dataset {ds.name}...")
            cls.con.execute(
                f"ALTER TABLE declaration_data "
                f"ADD COLUMN dataset_{ds.uuid} BOOLEAN DEFAULT FALSE"
            )

            # Collect all data first, then batch insert
            batch_data = []
            for module, name, kind, text, dependencies, type, initialProofState, is_in_dataset in ds._retrieve_all_declarations():
                batch_data.append((
                    cls._duckdb_escape(module),
                    cls._duckdb_escape(name),
                    cls._duckdb_escape(kind),
                    cls._duckdb_escape(text),
                    cls._duckdb_escape(str(dependencies)),
                    cls._duckdb_escape(type),
                    cls._duckdb_escape(initialProofState),
                    is_in_dataset
                ))

            # Execute batch insert if we have data
            if batch_data:
                cls.con.executemany(
                    f"INSERT INTO declaration_data (module, name, kind, text, dependencies, type, initialProofState, dataset_{ds.uuid}) "
                    f"VALUES (?, ?, ?, ?, ?, ?, ?, ?) "
                    f"ON CONFLICT (module, name) DO UPDATE SET "
                    f"dataset_{cls._duckdb_escape(ds.uuid)} = ?",
                    [(row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7], row[7]) for row in batch_data]
                )

    @classmethod
    def get_declaration(cls, module: Module, name: str):
        module.dataset._maybe_index_decls()
        res = cls.con.execute(f"SELECT * FROM declaration_data WHERE module = '{module.name}' AND name = '{cls._duckdb_escape(name)}' AND dataset_{module.dataset.uuid} = TRUE").fetchone()
        if res:
            columns = cls.con.table("declaration_data").columns
            res = {c: v for c, v in zip(columns, res) if not c.startswith("dataset_") and not c == "module"}
            return Declaration(module, res)

    @classmethod
    def get_module_declarations(cls, module: Module):
        module.dataset._maybe_index_decls()
        # assert module.dataset's section in the database is already build
        columns = cls.con.table("declaration_data").columns
        for decl_data in cls.con.execute(f"SELECT * FROM declaration_data WHERE module = '{module.name}'").fetchall():
            decl_data = {c : v for c, v in zip(columns, decl_data) if not c.startswith("dataset_") and not c == "module"}
            yield Declaration(module, decl_data)

    @classmethod
    def get_dataset_declarations(cls, ds: Dataset):
        ds._maybe_index_decls()
        columns = cls.con.table("declaration_data").columns
        mod_names_to_modules = {m.name: m for m in ds.modules}
        for decl_data in cls.con.execute(f"SELECT * FROM declaration_data WHERE dataset_{ds.uuid} = TRUE").fetchall():
            module_name = decl_data[columns.index("module")]
            assert module_name in mod_names_to_modules, f"Module {module_name} not found in dataset {ds.name}."
            decl_data = {c : v for c, v in zip(columns, decl_data) if not c.startswith("dataset_") and not c == "module"}
            yield Declaration(mod_names_to_modules[module_name], decl_data)

    @classmethod
    def retrieve_global(cls, module: Module, decl_name, attr, *args, **kwargs):
        if attr not in cls.attrs_map:
            raise ValueError(f"Attribute {attr} not registered for batch retrieval yet.")
        return cls.attrs_map[attr].retrieve(module, decl_name, attr, *args, **kwargs)

    @classmethod
    def fetch_all_dependency_strings(cls, ds: Dataset) -> Iterable[str]:
        """
        Fetch all dependency strings for the dataset.
        """
        ds._maybe_index_decls()
        for decl_data in cls.con.execute(f"SELECT dependencies FROM declaration_data WHERE dataset_{ds.uuid} = TRUE").fetchall():
            yield decl_data[0]

    def __init__(self, *attrs: str, default=None):
        self.attrs = attrs
        self.default = default
        for attr in attrs:
            assert not attr.startswith("dataset")
            if attr in BatchedRetriever.attrs_map:
                raise ValueError(f"Attribute {attr} already has a defined batching function")
            BatchedRetriever.attrs_map[attr] = self

    def __call__(self, operation):
        self.operation = operation
        self.initialize_table()
        return self.retrieve

    # ------------------------------------------------------------------ #
    # public API
    # ------------------------------------------------------------------ #

    def retrieve(self, module : Module, decl_name, attr, *args, **kwargs):
        assert attr not in ["module", "name"], "Attributes 'module' and 'name' are reserved and cannot be used."
        assert attr in self.attrs
        ds = module.dataset

        columns = self.con.table("declaration_data").columns

        decl_name = self._duckdb_escape(decl_name)
        res = self.con.execute(f"SELECT * FROM declaration_data WHERE module = '{module.name}' AND name = '{decl_name}'").fetchone()

        if not res or attr not in columns:
            # assert if it's value is missing this has in fact been populated already, an error has been raised earlier when _populating for the first time
            self._populate(ds, *args, **kwargs)
            columns = self.con.table("declaration_data").columns
            res = self.con.execute(
                f"SELECT * FROM declaration_data WHERE module = '{module.name}' AND name = '{decl_name}'").fetchone()

        if not res:
            raise ModuleNotFoundError(f"Declaration {decl_name} in module {module.name} not found in {ds.name}.")
            # warnings.warn(f"Declaration {decl_name} in module {module.name} not found in database for {top.name}.")

        res = {col: res[i] for i, col in enumerate(columns)}
        del res["module"]
        del res["name"]

        if attr not in res:
            warnings.warn(f"Attribute '{attr}' not found in declaration {decl_name} in module {module.name} in database for {ds.name}.")

        return res[attr]

    def _populate(self, ds: Dataset, *args, **kwargs) -> None:
        print(f"Caching results for {self.operation.__name__} on {ds.name}...")
        default = self.default
        gen = self.operation(ds, *args, **kwargs)
        batch_size = 1_000

        # ------------------------------------------------------------------ #
        # 1) first row → table setup
        # ------------------------------------------------------------------ #
        try:
            first_row = next(gen)
        except StopIteration:
            raise StopIteration("Population function didn't return anything")

        for attr in self.attrs:
            if attr not in first_row:
                raise TypeError(f"Attribute {attr} missing from the output of retrieval function {self.operation.__name__}")

        if default is not None:
            self._ensure_result_table(first_row, default_values={attr: default for attr in self.attrs})
        else:
            self._ensure_result_table(first_row)

        yielded_cols = first_row.copy().keys()
        assert "module" in yielded_cols and "name" in yielded_cols

        col_order = [r[0] for r in
                     self.con.execute(f"DESCRIBE declaration_data").fetchall()]

        # ------------------------------------------------------------------ #
        # 2) build an UPSERT that preserves old values
        # ------------------------------------------------------------------ #
        pk_cols = ["module", "name"]  # composite PK
        non_pk = [c for c in col_order if c not in pk_cols]

        placeholders = ", ".join("?" * len(col_order))
        update_clause = ", ".join(
            f"{c} = COALESCE(EXCLUDED.{c}, declaration_data.{c})"
            for c in non_pk
        )

        insert_sql = (
            f"INSERT INTO declaration_data "
            f"({', '.join(col_order)}) "
            f"VALUES ({placeholders}) "
            f"ON CONFLICT ({', '.join(pk_cols)}) DO UPDATE SET {update_clause}"
        )

        # ------------------------------------------------------------------ #
        # 3) helper to expand sparse dict → full row
        # ------------------------------------------------------------------ #
        def row_to_tuple(r: Mapping[str, object]) -> list[object]:
            return [r.get(c, None) for c in col_order]

        # ------------------------------------------------------------------ #
        # 4) stream in batches
        # ------------------------------------------------------------------ #
        batch: list[list[object]] = [row_to_tuple(first_row)]
        for row in gen:
            # assert row["name"] and row["module"]
            assert yielded_cols == row.keys()
            batch.append(row_to_tuple(row))
            if len(batch) >= batch_size:
                self.con.executemany(insert_sql, batch)
                batch.clear()

        if batch:
            self.con.executemany(insert_sql, batch)

        not_populated = self.con.execute(
                "SELECT * FROM declaration_data WHERE "
                f"dataset_{ds.uuid} = TRUE AND (" +
                    " OR ".join([f"{col} IS NULL" for col in yielded_cols])
                + ")"
            ).fetchall()
        if not default:
            if len(not_populated) > 0:
                raise ValueError(f"{len(not_populated)} declarations in {ds.name} were not mentioned by retrieval function {self.operation.__name__}")


    # ----------------------------------------------------------------------
    # Helper: create table (once) or evolve it when new columns appear
    # ----------------------------------------------------------------------
    def _ensure_result_table(self, sample_row: Mapping[str, object], default_values={}) -> None:
        assert "module" in sample_row and "name" in sample_row, "Sample row must contain 'module' and 'name' keys."

        existing_cols = {
            col[0]
            for col in self.con.execute(f"DESCRIBE declaration_data").fetchall()
        }
        for name, val in sample_row.items():
            if name not in existing_cols:
                if name in default_values:
                    if self._duck_type(val) == "TEXT":
                        self.con.execute(
                            f"ALTER TABLE declaration_data "
                            f"ADD COLUMN {name} {self._duck_type(val)} DEFAULT '{self._duckdb_escape(default_values[name])}'"
                        )
                    else:
                        self.con.execute(
                            f"ALTER TABLE declaration_data "
                            f"ADD COLUMN {name} {self._duck_type(val)} DEFAULT {self._duckdb_escape(default_values[name])}"
                        )
                else:
                    self.con.execute(
                        f"ALTER TABLE declaration_data "
                        f"ADD COLUMN {name} {self._duck_type(val)}"
                    )

    @staticmethod
    def _duck_type(value: Any) -> str:
        """Very small helper to map Python types to DuckDB types."""
        match value:
            case int():
                return "BIGINT"
            case float():
                return "DOUBLE"
            case bool():
                return "BOOLEAN"
            case _:
                return "TEXT"

    @staticmethod
    def _duckdb_escape(s):
        """
        Escape a string for use in a DuckDB query.
        """
        return s.replace("'", "''")


@BatchedRetriever("testcolumn", default="Default value for testcolumn")
def test(ds: Dataset) -> Iterable[Mapping[str, str]]:
    """
    Example function to test the BatchedRetriever.
    """
    for decl in ds.get_declarations():
        yield {
            "module": decl.module.name,
            "name": decl.name,
            "testcolumn": f"Test value for {decl.name} in {decl.module.name}"
        }


def _json_to_deps(decl : 'Declaration', raw):
    deps = []
    for dep in json.loads(raw):
        try:
            mod = Module(dep["module"], lean_dir=decl.module.lean_dir)
            mod.dataset = decl.module.dataset
            res = decl.module.dataset.get_declaration_from_identifiers(mod, dep["name"])
            if res:
                deps.append(res)
        except ModuleNotFoundError:
            pass
    return deps

_DECLARATION_LAZY_POSTPROCESS = {"dependencies": _json_to_deps}

class Declaration:
    def __init__(self, module: Module, initial_data: dict[str, str]):
        assert "name" in initial_data
        self.module = module
        for k, v in initial_data.items():
            object.__setattr__(self, k, v)

    def __getattribute__(self, item):
        if item in _DECLARATION_LAZY_POSTPROCESS:
            return _DECLARATION_LAZY_POSTPROCESS[item](self, object.__getattribute__(self, item))
        return object.__getattribute__(self, item)

    def __getattr__(self, item):
        # Value not yet retrieved
        if item not in BatchedRetriever.attrs_map:
            raise AttributeError(f"No registered attribute {item}")

        ret = BatchedRetriever.retrieve_global(self.module, self.name, item)
        object.__setattr__(self, item, ret)

        return object.__getattribute__(self, item)

    def __repr__(self):
        return self.name
    def __str__(self):
        return self.name

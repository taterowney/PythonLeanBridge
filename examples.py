from lean_python_bridge import Dataset, Module, LeanEnvironment


mod = Module("Examples") # Examples.lean from this directory
with LeanEnvironment(modules=[mod]) as b:
    print(b.run_command("testfn", 1))
    print(b.run_command("testfn", 0))
    for line in b.stream_output("effectful", 1):
        print(line)



Mathlib = Module("Mathlib")
my_module = Mathlib.Algebra.Group.Basic

ds = Dataset(modules=[my_module], name="Example Dataset")
# ds = ds.add_dependencies()
for decl in Mathlib.Algebra.Group.Basic.get_declarations():
    print(decl)
    print()
    print("Source code:")
    print(decl.text)
    print()
    print("Initial proof state:")
    print(decl.initialProofState)
    print()
    print("Dependencies:", decl.dependencies)
    print("============================")

This repo contains a draft of a dynamic FFI between Python and Lean. It works both ways: 
```python
with LeanEnvironment(modules=[Module("My.Module")]) as env:
	env.run_command("IO.println", "hello world!")
```

```lean4
PythonM.run (executable := "python") do
    commandResult "import time"
    let r : Float ← commandResult "time.time()"
    IO.println s!"Current time is: {r}"
```

It automatically bridges a few "primitive" types, as well as allowing for Lean interaction with arbitrary Python `object`s (the only real type in Python under the hood). More comprehensive examples can be found in `examples.py` and `Examples.lean`

**This project is under development and is kinda janky right now (I think there's still a few absolute paths somewhere in the code).

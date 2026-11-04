"""Differential checks against CPython 3.14.4; no third-party dependencies.

This test compiles source only as an independent oracle. Production extraction
remains external. Expected outcomes become Lean equations checked with
`decide +kernel`, not native_decide or solver trust.
"""

import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def lean_value(value):
    if value is None:
        return ".none"
    if type(value) is bool:
        return f".bool {str(value).lower()}"
    if type(value) is int:
        return f".int ({value})"
    raise TypeError(f"unsupported fixture value: {value!r}")


def lean_list(values):
    return "[" + ", ".join(lean_value(v) for v in values) + "]"


def artifact(name, function):
    code = function.__code__
    return f"""def {name} : Artifact :=
  {{ build := {json.dumps(sys.version)}
    name := {json.dumps(function.__name__)}
    code := {list(code.co_code)}
    constants := {lean_list(code.co_consts)}
    argCount := {code.co_argcount}
    posOnlyArgCount := {code.co_posonlyargcount}
    kwOnlyArgCount := {code.co_kwonlyargcount}
    localNames := {json.dumps(list(code.co_varnames))}
    names := {json.dumps(list(code.co_names))}
    freeVars := {json.dumps(list(code.co_freevars))}
    cellVars := {json.dumps(list(code.co_cellvars))}
    stackSize := {code.co_stacksize}
    flags := {code.co_flags}
    exceptionTable := {list(code.co_exceptiontable)} }}
"""


def expected(function, args):
    try:
        result = function(*args)
    except UnboundLocalError:
        return ".raised .unboundLocalError"
    except TypeError:
        return ".raised .typeError"
    return f".returned ({lean_value(result)})"


def main():
    if sys.implementation.name != "cpython" or sys.version_info[:3] != (3, 14, 4):
        raise SystemExit("This conformance test requires CPython 3.14.4 exactly.")

    namespace = runpy.run_path(str(ROOT / "examples/python/bytecode_slice.py"))
    values = [-10**40, -7, 0, 1, 3, 10**40, True, False, None]
    fixtures = {
        "add1": [(v,) for v in values],
        "countdown": [(v,) for v in [-5, 0, 1, 3, 7, True, False, None]],
        "choose": [(v, 123, False) for v in values],
        "checked": [(v,) for v in values],
        "literal": [()],
    }
    cases = [(name, namespace[name], args) for name, args in fixtures.items()]
    for index, operation in enumerate(["+", "-", "*", "<", "<=", "==", "!=", ">", ">="]):
        name = f"op_{index}"
        exec(compile(f"def {name}(n):\n return n {operation} 3\n", "<oracle>",
                     "exec", dont_inherit=True, optimize=0), namespace)
        cases.append((name, namespace[name], [(v,) for v in values]))
    for index, operation in enumerate(["+=", "-=", "*="]):
        name = f"inplace_{index}"
        exec(compile(f"def {name}(n):\n n {operation} 3\n return n\n", "<oracle>",
                     "exec", dont_inherit=True, optimize=0), namespace)
        cases.append((name, namespace[name], [(v,) for v in values]))
    for name, source in {
        "negated": "def negated(n):\n if not n:\n  return 1\n return 2\n",
        "branch_store": "def branch_store(n):\n if n:\n  x = 5\n else:\n  x = 9\n return x\n",
    }.items():
        exec(compile(source, "<oracle>", "exec", dont_inherit=True, optimize=0), namespace)
        cases.append((name, namespace[name], [(v,) for v in values]))

    lines = ["import BytecodeTests", "namespace VeriPyAsm.Conformance",
             "open Semantics CPython.V314 Examples Tests"]
    count = 0
    for name, function, inputs in cases:
        generated = f"actual_{name}"
        lines.append(artifact(generated, function))
        if name in fixtures:
            # Compare literal fixtures with real code objects, not just executions.
            # Build strings are provenance of the original extraction, not portable IDs.
            for field in ("code", "constants", "argCount", "posOnlyArgCount", "kwOnlyArgCount",
                          "localNames", "names", "freeVars", "cellVars", "stackSize", "flags",
                          "exceptionTable"):
                lines.append(f"example : {generated}.{field} = {name}Artifact.{field} := by decide +kernel")
        for args in inputs:
            lines.append(f"example : observe {generated} {lean_list(args)} = "
                         f".ok ({expected(function, args)}) := by decide +kernel")
            count += 1
    lines.append("end VeriPyAsm.Conformance")
    with tempfile.TemporaryDirectory(prefix="veripy-conformance-") as directory:
        path = Path(directory) / "Conformance.lean"
        path.write_text("\n\n".join(lines) + "\n")
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                capture_output=True, text=True)
        if result.returncode:
            print(result.stdout, end="")
            print(result.stderr, end="", file=sys.stderr)
            raise SystemExit(result.returncode)
    print(f"Passed: {count} CPython outcomes across {len(cases)} artifacts; "
          f"{len(fixtures)} literal fixtures matched code-object metadata.")


if __name__ == "__main__":
    main()

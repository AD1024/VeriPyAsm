"""Differential checks against CPython 3.14.4; no third-party dependencies.

This test compiles source only as an independent oracle. Production extraction
remains external. Expected outcomes become Lean equations checked with
`decide +kernel`, not native_decide or solver trust.
"""

from dataclasses import dataclass
import dis
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
from types import FunctionType


ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Case:
    name: str
    function: FunctionType
    inputs: list[tuple]
    required_opcodes: frozenset[str] = frozenset()
    wide_opcodes: frozenset[str] = frozenset()


def compiled_case(namespace, name, source, inputs, required=(), wide=()):
    exec(compile(source, "<oracle>", "exec", dont_inherit=True, optimize=0), namespace)
    return Case(name, namespace[name], inputs, frozenset(required), frozenset(wide))


def decoded_shape(case):
    """Use dis's independent prefix/cache-aware spans, never our decoder's output."""
    instructions = list(dis.get_instructions(case.function, adaptive=False))
    inventory = {instruction.opname for instruction in instructions}
    missing = case.required_opcodes - inventory
    assert not missing, f"{case.name}: missing required opcodes {sorted(missing)}"
    wide = {instruction.opname for instruction in instructions if (instruction.arg or 0) > 255}
    missing_wide = case.wide_opcodes - wide
    assert not missing_wide, f"{case.name}: missing wide operands for {sorted(missing_wide)}"
    return [(i.start_offset, i.opcode, i.arg if i.arg is not None else 0, i.end_offset)
            for i in instructions if i.opname != "EXTENDED_ARG"]


def budgeted(case, declaration):
    # Large code-object tables and their quadratic finite certificate checker
    # need a larger bounded budget. Small cases retain Lean's default limits.
    if case.wide_opcodes:
        return ("set_option maxRecDepth 20000 in\n"
                "set_option maxHeartbeats 20000000 in\n" + declaration)
    return declaration


def progress(message):
    # Lean normally collects stdout/stderr into messages until the file finishes.
    # With stderrAsMessages disabled below, this progress remains visible live.
    return ("run_elab do\n  let output ← IO.getStderr\n"
            f"  output.putStrLn {json.dumps(message)}\n  output.flush")


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


def artifact(name, function, *, optimize=0):
    code = function.__code__
    return f"""def {name} : Artifact :=
  {{ build := {json.dumps(sys.version)}
    optimize := {optimize}
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
    except AssertionError:
        return ".raised .assertionError"
    return f".returned ({lean_value(result)})"


def main():
    if sys.implementation.name != "cpython" or sys.version_info[:3] != (3, 14, 4):
        raise SystemExit("This conformance test requires CPython 3.14.4 exactly.")

    namespace = runpy.run_path(str(ROOT / "examples/python/bytecode_slice.py"))
    namespace["triangular"] = runpy.run_path(str(ROOT / "examples/python/triangular.py"))["triangular"]
    assertions = runpy.run_path(str(ROOT / "examples/python/assertions.py"))
    namespace.update({name: assertions[name] for name in ("nonnegative", "always_fails")})
    values = [-10**40, -7, 0, 1, 3, 10**40, True, False, None]
    fixtures = {
        "add1": [(v,) for v in values],
        "countdown": [(v,) for v in [-5, 0, 1, 3, 7, True, False, None]],
        "choose": [(v, 123, False) for v in values],
        "checked": [(v,) for v in values],
        "literal": [()],
        "triangular": [(v,) for v in [-3, 0, 1, 3, 6, True, False, None]],
        "nonnegative": [(v,) for v in values],
        "always_fails": [()],
    }
    cases = [Case(name, namespace[name], args,
                  frozenset({"LOAD_FAST_BORROW_LOAD_FAST_BORROW"}) if name == "triangular" else frozenset())
             for name, args in fixtures.items()]
    for index, operation in enumerate(["+", "-", "*", "<", "<=", "==", "!=", ">", ">="]):
        name = f"op_{index}"
        cases.append(compiled_case(namespace, name, f"def {name}(n):\n return n {operation} 3\n",
                                   [(v,) for v in values]))
    for index, operation in enumerate(["+=", "-=", "*="]):
        name = f"inplace_{index}"
        cases.append(compiled_case(namespace, name, f"def {name}(n):\n n {operation} 3\n return n\n",
                                   [(v,) for v in values]))
    for name, source in {
        "negated": "def negated(n):\n if not n:\n  return 1\n return 2\n",
        "branch_store": "def branch_store(n):\n if n:\n  x = 5\n else:\n  x = 9\n return x\n",
    }.items():
        cases.append(compiled_case(namespace, name, source, [(v,) for v in values]))

    assertion_opcodes = {"LOAD_COMMON_CONSTANT", "RAISE_VARARGS"}
    for name, source in {
        "assert_truthy": "def assert_truthy(n):\n assert n\n return n\n",
        "assert_not": "def assert_not(n):\n assert not n\n return n\n",
        "assert_unbound": "def assert_unbound(n):\n if n:\n  x=1\n assert x\n return 0\n",
    }.items():
        cases.append(compiled_case(namespace, name, source, [(v,) for v in values],
                                   required=assertion_opcodes))
    cases.extend([
        compiled_case(namespace, "assert_and",
                      "def assert_and(n,m):\n assert n>=0 and m>0\n return n\n",
                      [(0, 1), (-1, None), (0, None), (1, 0), (True, True), (False, True), (None, 1)],
                      required=assertion_opcodes),
        compiled_case(namespace, "assert_or",
                      "def assert_or(n,m):\n assert n>=0 or m>0\n return n\n",
                      [(0, None), (-1, 1), (-1, 0), (-1, None), (None, 1), (True, None), (False, None)],
                      required=assertion_opcodes),
        compiled_case(namespace, "assert_in_loop",
                      "def assert_in_loop(n):\n s=0\n while n>0:\n  s=s+n\n  n=n-1\n  assert n>=0\n return s\n",
                      [(v,) for v in [-2, 0, 1, 3, 6, True, False, None]], required=assertion_opcodes),
    ])

    pairs = [(3, 9), (-7, 2), (True, False), (None, 1)]
    cases.extend([
        compiled_case(namespace, "fused_load", "def fused_load(a,b):\n return a+b\n", pairs,
                      required={"LOAD_FAST_BORROW_LOAD_FAST_BORROW"}),
        compiled_case(namespace, "fused_swap", "def fused_swap(a,b):\n a,b=b,a\n return a-b\n", pairs,
                      required={"LOAD_FAST_LOAD_FAST", "STORE_FAST_STORE_FAST"}),
        compiled_case(namespace, "store_load", "def store_load(a,b,c):\n a=b; b=c\n return a-b\n",
                      [(0, 9, 2), (0, True, False), (0, None, 1)], required={"STORE_FAST_LOAD_FAST"}),
        compiled_case(namespace, "store_load_alias", "def store_load_alias(a,b):\n a=1; b=a\n return b\n",
                      [(None, None), (7, 9)], required={"STORE_FAST_LOAD_FAST"}),
        compiled_case(namespace, "wide_local",
                      "def wide_local(" + ",".join(f"a{i}" for i in range(257)) +
                      "):\n a256=7\n return a256\n", [tuple(range(257))],
                      required={"EXTENDED_ARG"}, wide={"STORE_FAST", "LOAD_FAST_BORROW"}),
        compiled_case(namespace, "wide_constant",
                      "def wide_constant():\n" + "".join(f" x={1000+i}\n" for i in range(257)) +
                      " return x\n", [()], required={"EXTENDED_ARG"}, wide={"LOAD_CONST"}),
        compiled_case(namespace, "wide_loop",
                      "def wide_loop(n):\n x=1\n while n>0:\n" + "  x=x+1\n" * 32 +
                      "  n=n-1\n return x\n", [(0,), (1,), (2,), (-1,)],
                      required={"EXTENDED_ARG"}, wide={"POP_JUMP_IF_FALSE", "JUMP_BACKWARD"}),
    ])

    lines = ["import BytecodeTests", "import VeriPyAsm.Examples.Triangular",
             "import VeriPyAsm.Examples.Assertions.Artifact",
             "import VeriPyAsm.Verification.AxiomAudit",
             "set_option Elab.async false", "set_option stderrAsMessages false",
             "namespace VeriPyAsm.Conformance",
             "open Semantics CPython.V314 Examples Tests"]
    lines.append(progress("Checking source corpus against CPython 3.14.4"))
    count = 0
    instruction_count = 0
    for case in cases:
        name, function, inputs = case.name, case.function, case.inputs
        generated = f"actual_{name}"
        if case.wide_opcodes:
            lines.append(progress(f"Checking extended operands: {name}"))
        lines.append(budgeted(case, artifact(generated, function)))
        lines.append(budgeted(case, f"def admitted_{name} : Admitted {generated} := admit_bytecode% {generated}"))
        if case.wide_opcodes:
            lines.append(progress(f"Stack and ownership admission checked: {name}"))
        shape = decoded_shape(case)
        instruction_count += len(shape)
        lines.append(budgeted(case,
            f"example : admitted_{name}.translation.code.instructions.map "
            f"(fun i => (i.offset, i.opcode, i.arg, i.next)) = {shape} := by decide +kernel"))
        if name in fixtures:
            # Compare literal fixtures with real code objects, not just executions.
            # Build strings are provenance of the original extraction, not portable IDs.
            fixture = {"nonnegative": "Assertions.nonnegativeArtifact",
                       "always_fails": "Assertions.alwaysFailsArtifact"}.get(name, f"{name}Artifact")
            for field in ("code", "constants", "argCount", "posOnlyArgCount", "kwOnlyArgCount",
                          "localNames", "names", "freeVars", "cellVars", "stackSize", "flags",
                          "exceptionTable"):
                lines.append(f"example : {generated}.{field} = {fixture}.{field} := by decide +kernel")
        for args in inputs:
            lines.append(budgeted(case, f"example : observe {generated} {lean_list(args)} = "
                         f".ok ({expected(function, args)}) := by decide +kernel"))
            count += 1
    # These are real compiler outputs, but outside the current assertion profile.
    # Compile them to inspect bytes; never execute a rejected artifact here.
    rejected = [
        compiled_case(namespace, "assert_message",
                      "def assert_message(n):\n assert n, 1\n return n\n", [], required={"CALL"}),
        compiled_case(namespace, "assert_folded",
                      "def assert_folded(n):\n assert True\n return n\n", [], required={"NOP"}),
        compiled_case(namespace, "raise_argument", "def raise_argument(n):\n raise n\n", [],
                      required={"RAISE_VARARGS"}),
    ]
    for case in rejected:
        decoded_shape(case)
        generated = f"rejected_{case.name}"
        lines.append(artifact(generated, case.function))
        lines.append(f"example : (decode {generated}).isOk = false := by decide +kernel")
    optimized = compile("def optimized(n):\n assert n\n return n\n", "<oracle>", "exec",
                        dont_inherit=True, optimize=1)
    function = FunctionType(next(c for c in optimized.co_consts if hasattr(c, "co_code")), {})
    assert "RAISE_VARARGS" not in {i.opname for i in dis.get_instructions(function)}
    lines.append(artifact("rejected_optimized", function, optimize=1))
    lines.append("example : (decode rejected_optimized).isOk = false := by decide +kernel")
    lines.append("end VeriPyAsm.Conformance")
    lines.append("#veripy_audit VeriPyAsm.Conformance")
    with tempfile.TemporaryDirectory(prefix="veripy-conformance-") as directory:
        path = Path(directory) / "Conformance.lean"
        path.write_text("\n\n".join(lines) + "\n")
        # Stream Lean diagnostics, including progress on the large artifacts.
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT)
        if result.returncode:
            raise SystemExit(result.returncode)
    print(f"Passed: {count} CPython outcomes across {len(cases)} stack/ownership-admitted artifacts; "
          f"{len(fixtures)} literal fixtures matched code-object metadata; "
          f"{instruction_count} decoded instruction spans matched dis; "
          f"{len(rejected) + 1} unsupported assertion/raise forms rejected.")


if __name__ == "__main__":
    main()

"""CI entry point: build regressions, audit every project module, check CPython.

Run with the pinned CPython 3.14.4. No third-party Python dependencies. Crush
experiments are optional because their solver executable is a separate tool.
"""

import argparse
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib


ROOT = Path(__file__).resolve().parents[1]


def run(*arguments):
    subprocess.run(arguments, cwd=ROOT, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--with-crush", action="store_true", help="also require the cvc5 proof targets")
    args = parser.parse_args()
    if sys.implementation.name != "cpython" or sys.version_info[:3] != (3, 14, 4):
        raise SystemExit("CI checks require CPython 3.14.4 exactly.")

    configuration = tomllib.loads((ROOT / "lakefile.toml").read_text())
    regressions = [library["name"] for library in configuration["lean_lib"]
                   if library.get("srcDir") == "tests"]
    # Discover modules too: a new exported certificate must not escape auditing
    # simply because nobody has added its import to the umbrella module yet.
    modules = ["VeriPyAsm"] + sorted(
        ".".join(path.relative_to(ROOT).with_suffix("").parts)
        for path in (ROOT / "VeriPyAsm").rglob("*.lean"))
    experiments = [library["name"] for library in configuration["lean_lib"]
                   if args.with_crush and library.get("srcDir") == "experiments"]
    targets = modules + regressions + experiments
    print(f"Building {len(modules)} project modules and {len(regressions)} regression libraries", flush=True)
    run("lake", "build", *targets)

    with tempfile.TemporaryDirectory(prefix="veripyasm-ci-audit-") as directory:
        path = Path(directory) / "Audit.lean"
        path.write_text("\n".join(f"import {module}" for module in targets)
                        + "\n#veripy_audit VeriPyAsm\n")
        run("lake", "env", "lean", str(path))

    run(sys.executable, str(ROOT / "tests/check_cpython.py"))
    print("Passed: Lean regressions, transitive axiom audit, and CPython conformance", flush=True)


if __name__ == "__main__":
    main()

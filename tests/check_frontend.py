"""Source extraction, mapping, and generated-proof integration regressions."""

import ast
import base64
import dis
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import FunctionType
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from veripy_frontend.__main__ import run_lean, write_generated
from veripy_frontend.emit import emit
from veripy_frontend.source import FrontendError, Parser, extract


EXAMPLE = ROOT / "examples/python/triangular_annotated.py"
SOURCE = EXAMPLE.read_text()
NESTED = (ROOT / "examples/python/nested_product_annotated.py").read_text()


class SourceFrontendTests(unittest.TestCase):
    def parse(self, source=SOURCE, *, inspection=False):
        return Parser("fixture.py", source.encode()).parse("triangular", inspection=inspection)

    def nested(self, source=NESTED, name="nested_product", *, inspection=False):
        return Parser("nested.py", source.encode()).parse(name, inspection=inspection)

    def prove_scoped(self, function, namespace):
        text = emit(function, namespace).replace("import VeriPyAsm.Frontend.Mapping",
            "import VeriPyAsm.Verification.VC.Discharge\nimport VeriPyAsm.Frontend.Mapping")
        names = [f"p{i}" for i in range(len(function.parameters))]
        arguments = "[" + ", ".join(f".int {name}" for name in names) + "]"
        text += f"""
namespace {namespace}
set_option maxHeartbeats 8000000
@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro {' '.join(names)}
  intros
  exact ⟨{arguments}, rfl, rfl⟩
@[veripy_proof generated.VC.execution]
theorem execution : generated.VC.execution := by
  unfold generated.VC.execution
  grind
set_option veripy.auto false in
veripy_verify verified from generated
example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
#veripy_audit {namespace}
end {namespace}
"""
        return run_lean(text)

    def test_compile_only_and_lossless_artifact(self):
        function = self.parse(SOURCE + "\nraise RuntimeError('must not execute module')\n")
        bundle = function.bundle()
        self.assertEqual(base64.b64decode(bundle["sourceBytesBase64"]), function.raw)
        self.assertEqual(bundle["artifact"]["code"], list(function.code.co_code))
        self.assertEqual(len(bundle["source"]["positions"]), len(function.code.co_code) // 2)
        runtime = FunctionType(function.code, {})
        for n in range(101):
            self.assertEqual(runtime(n), n*(n+1)//2)
        large = self.parse(SOURCE.replace("s = 0", "s = 1234567890123456789012345678901234567890"))
        self.assertIn({"tag": "int", "value": "1234567890123456789012345678901234567890"},
                      large.bundle()["artifact"]["constants"])

    def test_rejects_missing_type_guards_and_annotations(self):
        for source, diagnostic in [
            (SOURCE.replace("is_int(n) and n >= 0", "n >= 0"), "explicit is_int"),
            (SOURCE.replace("is_int(n) and n >= 0", "is_int(n) or True"), "explicit is_int"),
            (SOURCE.replace("# veripy: ensures", "# disabled: ensures"), "missing ensures"),
            (SOURCE.replace("# veripy: invariant", "# disabled: invariant"), "missing loop invariant"),
            (SOURCE.replace("# veripy: decreases", "# disabled: decreases"), "requires decreases"),
        ]:
            with self.subTest(diagnostic=diagnostic), self.assertRaisesRegex(FrontendError, diagnostic):
                self.parse(source)
        original = (ROOT / "examples/python/triangular.py").read_text()
        inspected = self.parse(original, inspection=True)
        self.assertEqual(len(inspected.missing), 4)

    def test_assertions_and_hints_are_not_silently_ignored(self):
        for source, diagnostic in [
            (SOURCE.replace("        n = n - 1", "        n = n - 1\n        assert n >= 0"), "source proof checkpoints"),
            (SOURCE.replace("        n = n - 1", "        n = n - 1\n        # veripy: prove p: n >= 0"), "unsupported annotation"),
            (SOURCE.replace("# veripy: decreases n", "# veripy: decreases n\n    # veripy: invariantz True"), "cannot annotate"),
            (SOURCE + "    # veripy: invariant True\n", "unsupported annotation"),
            (SOURCE.replace("s = 0", "s = 0  # veripy: invariant True"), "unsupported annotation"),
        ]:
            with self.subTest(diagnostic=diagnostic), self.assertRaisesRegex(FrontendError, diagnostic):
                self.parse(source)

    def test_rejects_unsupported_or_ambiguous_source(self):
        mutations = [
            (SOURCE.replace("s = 0", "s = int(n)"), "unsupported Python expression"),
            (SOURCE.replace("s = 0", "s = missing"), "uninitialized name"),
            (SOURCE.replace("invariant n >= 0", "invariant missing >= 0"), "uninitialized name"),
            (SOURCE.replace("old(n)", "old(s)"), "parameter name"),
            (SOURCE.replace("def triangular(n):", "def triangular(n=3):"), "defaults"),
            (SOURCE.replace("        s = s + n", "        while n > 1:\n            n = n - 1\n        s = s + n"), "missing loop invariant"),
            (SOURCE.replace("s = 0", "s = 0; n = n + 0"), "semicolon"),
            (SOURCE.replace("    # veripy: decreases n", "    # veripy: decreases n\n    # veripy: decreases n"), "duplicate decreases"),
            (SOURCE.replace("    # veripy: invariant n", "# veripy: invariant n"), "indentation"),
            (SOURCE.replace("def triangular(n):", "def triangular(result):"), "reserved logical"),
        ]
        for source, diagnostic in mutations:
            with self.subTest(diagnostic=diagnostic), self.assertRaisesRegex(FrontendError, diagnostic):
                self.parse(source)
        with self.assertRaisesRegex(FrontendError, "exactly one"):
            self.parse(SOURCE + "\ndef triangular(n):\n    return n\n")

    def test_partial_mode_is_explicit(self):
        source = SOURCE.replace("# veripy: requires", "# veripy: mode partial\n# veripy: requires")
        with self.assertRaisesRegex(FrontendError, "partial mode"):
            self.parse(source)
        partial = self.parse(source.replace("    # veripy: decreases n\n", ""))
        self.assertIsNone(partial.decreases)
        self.assertIn(".partialCorrectness", emit(partial, "PartialSource"))

    def test_other_functions_do_not_capture_selected_annotations(self):
        source = SOURCE + '''
# veripy: requires is_int(x)
# veripy: ensures result == old(x)
def other(x):
    return x
'''
        self.assertEqual(self.parse(source).label, "sum_loop")

    def test_checked_mapping_matches_disassembler_and_recompiles(self):
        function = self.parse()
        original = run_lean(emit(function, "MappingOriginal", mapping_only=True))
        self.assertEqual(original["header"], 6)
        instructions = list(dis.get_instructions(function.code, adaptive=False))
        backward = next(i for i in instructions if i.opname == "JUMP_BACKWARD")
        self.assertEqual(original["backedges"], [{"sourcePC": backward.offset, "targetPC": backward.argval}])
        changed = self.parse(SOURCE.replace("s = 0", "s = n - n"))
        mapped = run_lean(emit(changed, "MappingChanged", mapping_only=True))
        self.assertNotEqual(mapped["header"], original["header"])
        self.assertNotEqual(changed.bundle()["artifactDigest"], function.bundle()["artifactDigest"])
        self.assertEqual(mapped["header"], next(i.argval for i in dis.get_instructions(changed.code)
                                              if i.opname == "JUMP_BACKWARD"))

    def test_multiline_unicode_and_short_circuit_condition(self):
        source = re.sub(r"\bn\b", "entrée", SOURCE)
        source = source.replace("while entrée > 0:", "while (entrée > 0\n           and entrée >= 1):")
        function = self.parse(source)
        mapping = run_lean(emit(function, "UnicodeSource", mapping_only=True))
        self.assertEqual(mapping["header"], 6)
        self.assertEqual(len(mapping["exitEdges"]), 2)
        self.assertIn("entrée", function.bundle()["artifact"]["localNames"])
        name = function.loop.test.values[0].left
        self.assertEqual(name.end_col_offset - name.col_offset, len("entrée".encode("utf-8")))

    def test_two_parameters_and_final_local_reads_elaborate(self):
        source = SOURCE.replace("def triangular(n):", "def triangular(n, m):")
        source = source.replace("requires is_int(n)", "requires is_int(m) and is_int(n)")
        source = source.replace("# veripy: ensures is_int(result)", "# veripy: ensures n == 0 and m == old(m) and is_int(result)")
        function = self.parse(source)
        mapping = run_lean(emit(function, "TwoParameters"))
        self.assertEqual(mapping["header"], 6)

    def test_short_circuit_or_has_distinct_entries_and_unique_region(self):
        function = self.parse(SOURCE.replace("while n > 0:", "while n > 0 or n > 1:"))
        text = emit(function, "OrCondition").replace("import VeriPyAsm.Frontend.Mapping",
            "import VeriPyAsm.Verification.VC.Discharge\nimport VeriPyAsm.Frontend.Mapping")
        text += '''
namespace OrCondition
@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro n _
  exact ⟨[.int n], rfl, rfl⟩
@[veripy_proof generated.VC.init]
theorem init : generated.VC.init := True.intro
@[veripy_proof generated.VC.cut6]
theorem preserve : generated.VC.cut6 := by
  intro n _ current _ counter sum _ nonnegative equation
  split
  · grind
  · have zero : counter = 0 := by omega
    subst counter
    simpa using equation
set_option veripy.auto false in
veripy_verify verified from generated
example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
#veripy_audit OrCondition
end OrCondition
'''
        mapping = run_lean(text)
        self.assertEqual(len(mapping["bodyEdges"]), 2)
        self.assertEqual(mapping["bodyEdges"][0]["targetPC"], mapping["bodyEdges"][1]["targetPC"])
        self.assertEqual(len(mapping["bodyNodes"]), len(set(mapping["bodyNodes"])))

    def test_negative_measure_leaves_a_false_vc(self):
        function = self.parse(SOURCE.replace("decreases n", "decreases -1"))
        text = emit(function, "NegativeMeasure")
        text = text.replace("import VeriPyAsm.Frontend.Mapping", "import VeriPyAsm.Verification.VC.Discharge\nimport VeriPyAsm.Frontend.Mapping")
        text += '''
namespace NegativeMeasure
example : ¬ generated.VC.init := by
  simp [generated.VC.init]
  exact ⟨0, by decide⟩
set_option veripy.auto false in
veripy_discover pending from generated
example : pending.report.complete = false := rfl
end NegativeMeasure
'''
        run_lean(text)

    def test_nested_local_initialization_mapping_and_runtime(self):
        function = self.nested()
        self.assertEqual([loop.parent for loop in function.loops], [None, 0])
        self.assertNotIn("j", function.loops[0].header_names)
        self.assertIn("j", function.loops[1].header_names)
        self.assertEqual(function.loops[1].modified_names, {"total", "j"})
        runtime = FunctionType(function.code, {})
        for n in range(8):
            for m in range(8):
                self.assertEqual(runtime(n, m), n*m)
        mapping = run_lean(emit(function, "NestedMapping", mapping_only=True))
        self.assertEqual(mapping["parents"], [None, 0])
        backwards = {(i.offset, i.argval) for i in dis.get_instructions(function.code)
                     if i.opname == "JUMP_BACKWARD"}
        self.assertEqual({(e["sourcePC"], e["targetPC"]) for loop in mapping["loops"]
                          for e in loop["backedges"]}, backwards)
        self.assertFalse(set(mapping["loops"][0]["testNodes"]) & set(mapping["loops"][1]["testNodes"]))

    def test_nested_annotations_are_scoped_and_required(self):
        for source, diagnostic in [
            (NESTED.replace("# veripy: invariant j", "# disabled: invariant j"), "missing loop invariant"),
            (NESTED.replace("# veripy: decreases j", "# disabled: decreases j"), "requires decreases"),
            (NESTED.replace("loop columns", "loop rows"), "duplicate loop label"),
            (NESTED.replace("invariant i >= 0", "invariant j >= 0"), "uninitialized name"),
            (NESTED.replace("return total", "return j"), "uninitialized name"),
            (NESTED.replace("j = j - 1", "continue"), "unsupported statement"),
        ]:
            with self.subTest(diagnostic=diagnostic), self.assertRaisesRegex(FrontendError, diagnostic):
                self.nested(source)
        unannotated = re.sub(r"^.*# veripy:.*\n", "", NESTED, flags=re.M)
        inspected = self.nested(unannotated, inspection=True)
        self.assertEqual(sum("invariant" in item for item in inspected.missing), 2)
        self.assertEqual(sum("decreases" in item for item in inspected.missing), 2)

    def test_outer_measure_can_decrease_before_inner_entry(self):
        source = NESTED.replace("        i = i - 1\n", "")
        source = source.replace("        j = m", "        i = i - 1\n        j = m")
        source = source.replace("(old(n) - i) * old(m) +", "(old(n) - i - 1) * old(m) +")
        function = self.nested(source)
        mapping = self.prove_scoped(function, "DecreaseBeforeInner")
        self.assertEqual(mapping["parents"], [None, 0])

    def test_three_nested_loops_and_sequential_reset(self):
        source = """# veripy: requires is_int(n) and n >= 0
# veripy: ensures result == 0
def countdown(n):
    i = n
    # veripy: invariant i >= 0
    # veripy: decreases i
    while i > 0:
        j = n
        # veripy: invariant j >= 0
        # veripy: decreases j
        while j > 0:
            k = n
            # veripy: invariant k >= 0
            # veripy: decreases k
            while k > 0:
                k = k - 1
            j = j - 1
        i = i - 1
    i = n
    # veripy: invariant i >= 0
    # veripy: decreases i
    while i > 0:
        i = i - 1
    return i
"""
        function = self.nested(source, "countdown")
        mapping = self.prove_scoped(function, "DeepAndSequential")
        self.assertEqual(mapping["parents"], [None, 0, 1, None])
        runtime = FunctionType(function.code, {})
        for n in range(5):
            self.assertEqual(runtime(n), 0)

    def test_invalid_inner_measure_keeps_execution_pending(self):
        for measure in ("-1", "0"):
            with self.subTest(measure=measure):
                function = self.nested(NESTED.replace("decreases j", f"decreases {measure}"))
                text = emit(function, "InvalidInnerMeasure").replace("import VeriPyAsm.Frontend.Mapping",
                    "import VeriPyAsm.Verification.VC.Discharge\nimport VeriPyAsm.Frontend.Mapping")
                text += """
namespace InvalidInnerMeasure
open VeriPyAsm.Semantics
@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro n m _ _ _ _
  exact ⟨[.int n, .int m], rfl, rfl⟩
example : ¬ generated.VC.execution := by
  intro valid
  have outer := valid 1 1
    { locals := [some (.int 1), some (.int 1), none, none, none] }
    (by decide) (by decide) rfl
  have inner := outer
    { pc := map0.header, locals := [some (.int 1), some (.int 1), some (.int 1), some (.int 0), none] }
    rfl 1 1 1 0 none rfl (by decide) (by decide) rfl rfl
"""
                if measure == "0":
                    text += """
  dsimp at inner
  have impossible := inner
    { pc := map1.header, locals := [some (.int 1), some (.int 1), some (.int 1), some (.int 0), some (.int 1)] }
    rfl 1 1 1 0 1 rfl (by decide) (by decide) rfl rfl rfl
"""
                text += """
  omega
set_option veripy.auto false in
veripy_discover pending from generated
example : pending.report.complete = false := rfl
#veripy_audit InvalidInnerMeasure
end InvalidInnerMeasure
"""
                run_lean(text)

    def test_nested_partial_mode_and_branch(self):
        source = NESTED.replace("# veripy: requires", "# veripy: mode partial\n# veripy: requires")
        source = re.sub(r"^.*# veripy: decreases.*\n", "", source, flags=re.M)
        # A conditional inner loop still has the same lexical parent.
        start = source.index("        j = m")
        end = source.index("        i = i - 1")
        source = source[:start] + "        if m >= 0:\n" + "".join(
            "    " + line for line in source[start:end].splitlines(keepends=True)) + source[end:]
        function = self.nested(source)
        mapping = self.prove_scoped(function, "NestedPartialBranch")
        self.assertEqual(mapping["parents"], [None, 0])

    def test_missing_debug_ranges_rejected_by_lean(self):
        result = subprocess.run([sys.executable, "-X", "no_debug_ranges", "-m", "veripy_frontend",
                                 "inspect", str(EXAMPLE), "--function", "triangular"], cwd=ROOT,
                                text=True, capture_output=True, timeout=180)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unique while header", result.stderr)
        self.assertNotIn("checked loop header", result.stdout)

    def test_generated_output_preserves_user_files(self):
        function = self.parse()
        with tempfile.TemporaryDirectory(prefix="veripy-output-test-") as temporary:
            path = Path(temporary) / "Proofs.lean"
            path.write_text("-- User proof\n")
            with self.assertRaisesRegex(FrontendError, "user-owned"):
                write_generated(path, emit(function, "Output"), function.bundle())
            self.assertEqual(path.read_text(), "-- User proof\n")

    def test_committed_example_matches_source_and_contains_no_manual_offsets(self):
        function = extract(Path("examples/python/triangular_annotated.py"), "triangular")
        generated = emit(function, "VeriPyAsm.Examples.SourceTriangular")
        actual = (ROOT / "VeriPyAsm/Examples/SourceTriangular/Generated.lean").read_text()
        # Build provenance can vary across installations of the pinned release.
        def without_build(text):
            return re.sub(r'^  build := .*$', '  build := "<interpreter-build>"', text, flags=re.M)
        self.assertEqual(without_build(generated), without_build(actual))
        self.assertIn("cutpoints := [sourceMap.header]", generated)
        self.assertNotIn("cutpoints := [6]", generated)
        function = extract(Path("examples/python/nested_product_annotated.py"), "nested_product")
        generated = emit(function, "VeriPyAsm.Examples.SourceNestedProduct")
        actual = (ROOT / "VeriPyAsm/Examples/SourceNestedProduct/Generated.lean").read_text()
        self.assertEqual(without_build(generated), without_build(actual))
        self.assertIn("loops := [loop0, loop1]", generated)
        self.assertIn("sourceMaps.loops[1]!", generated)


if __name__ == "__main__":
    unittest.main(verbosity=2)

"""End-to-end checkpoints through scoped loop summaries and their continuations."""

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
from veripy_frontend.__main__ import run_lean
from veripy_frontend.emit import emit
from frontend_proofs import scoped_providers
from veripy_frontend.source import Parser

EXAMPLE = ROOT / "examples/python/nested_product_checkpoints.py"
SOURCE = EXAMPLE.read_text()

SINGLE = '''# veripy: requires is_int(n) and n >= 0
# veripy: ensures result == 0
def countdown(n):
    # veripy: invariant n >= 0
    # veripy: decreases n
    while n > 0:
        s = n
        n = n - 1
        # veripy: prove changed: s == n + 1
    return n
'''

SEQUENTIAL = '''# veripy: requires is_int(n) and is_int(m) and n >= 0 and m >= 0
# veripy: ensures result == 0
def consume(n, m):
    # veripy: invariant n >= 0 and m == old(m)
    # veripy: decreases n
    while n > 0:
        n = n - 1
        # veripy: prove first: n >= 0
    # veripy: invariant n == 0 and m >= 0
    # veripy: decreases m
    while m > 0:
        m = m - 1
        # veripy: prove second: m >= 0
    # veripy: prove done: n + m == 0
    return n + m
'''


def providers(function, entry, exclude=()):
    result = f'''
@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  {entry}
'''
    result += scoped_providers(exclude)
    for field in ["checkpoint_" + c.label for c in function.checkpoints]:
        if field in exclude:
            continue
        result += f'''
@[veripy_proof generated.VC.{field}]
theorem proof_{field} : generated.VC.{field} := by
  unfold generated.VC.{field}
  grind
'''
    return result


def nested_counterexample(goal, m, total, counter):
    """Reach an inner header from a positive outer header, then inspect its VC."""
    return f'''
theorem rejected : ¬ generated.VC.{goal} := by
  intro valid
  have outer := valid 1 {m} _ (by decide) (by decide) rfl
  have inner := outer
    {{ pc := map0.header, locals := [some (.int 1), some (.int {m}), some (.int 1), some (.int 0), none] }}
    rfl 1 {m} 1 0 none rfl (by decide) rfl rfl rfl (by decide)
  have impossible := inner
    {{ pc := map1.header, locals := [some (.int 1), some (.int {m}), some (.int 1), some (.int {total}), some (.int {counter})] }}
    rfl 1 {m} 1 {total} {counter} rfl (by decide) rfl rfl rfl rfl
  simp at impossible
'''


class ScopedCheckpointTests(unittest.TestCase):
    def parse(self, source=SOURCE, name="nested_product"):
        return Parser("scoped.py", source.encode()).parse(name)

    def check(self, function, namespace, proof):
        return run_lean("import VeriPyAsm.Verification.VC.Discharge\n" + emit(function, namespace) +
                        f"\nnamespace {namespace}\n" + proof +
                        f"\n#veripy_audit {namespace}\nend {namespace}\n")

    def verify(self, function, namespace, entry):
        return self.check(function, namespace, providers(function, entry) + '''
set_option veripy.auto false in
veripy_verify verified from generated
example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
''')

    def test_committed_example_and_cpython_zero_one_many_iterations(self):
        function = Parser("examples/python/nested_product_checkpoints.py", EXAMPLE.read_bytes()).parse("nested_product")
        directory = ROOT / "VeriPyAsm/Examples/SourceNestedCheckpoints"
        without_build = lambda text: re.sub(r'^  build := .*$', '', text, flags=re.M)
        self.assertEqual(without_build(emit(function, "VeriPyAsm.Examples.SourceNestedCheckpoints")),
                         without_build((directory / "Generated.lean").read_text()))
        stored = json.loads((directory / "Generated.source.json").read_text())
        fresh = function.bundle()
        self.assertEqual(stored["directives"], fresh["directives"])
        self.assertEqual(stored["sourceBytesBase64"], fresh["sourceBytesBase64"])
        for key in fresh["artifact"]:
            if key != "build":
                self.assertEqual(stored["artifact"][key], fresh["artifact"][key], key)
        runtime = FunctionType(function.code, {})
        for n in range(5):
            for m in range(5):
                self.assertEqual(runtime(n, m), n * m)

    def test_cli_links_each_nested_checkpoint_to_its_mandatory_vc(self):
        with tempfile.TemporaryDirectory(prefix="veripy-scoped-checkpoints-") as directory:
            output = Path(directory) / "Generated.lean"
            result = subprocess.run([sys.executable, "-m", "veripy_frontend", "generate", str(EXAMPLE),
                                     "--function", "nested_product", "--namespace", "NestedChecks",
                                     "--output", str(output), "--json"],
                                    cwd=ROOT, text=True, capture_output=True, timeout=180)
            self.assertEqual(result.returncode, 0, result.stderr)
            bundle = json.loads(result.stdout)
            self.assertEqual(bundle, json.loads(output.with_suffix(".source.json").read_text()))
            self.assertEqual(bundle["status"], "vcs_generated")
            self.assertEqual(bundle["mapping"]["loopMapping"]["parents"], [None, 0])
            self.assertEqual([c["vcGoal"] for c in bundle["checkpoints"]["items"]],
                             ["NestedChecks.generated.VC.checkpoint_" + c.label for c in self.parse().checkpoints])
            self.assertIn("VC.ScopedCheckpointSpecification", output.read_text())

    def test_single_loop_with_an_initially_uninitialized_local(self):
        function = self.parse(SINGLE, "countdown")
        self.assertTrue(function.scoped)
        self.verify(function, "Single", "intro n _; exact ⟨[.int n], rfl, rfl⟩")

    def test_sequential_summaries_keep_both_loop_obligations(self):
        function = self.parse(SEQUENTIAL, "consume")
        self.assertTrue(function.scoped)
        mapping = self.verify(function, "Sequential",
                              "intro n m _ _ _ _; exact ⟨[.int n, .int m], rfl, rfl⟩")
        self.assertEqual(mapping["loopMapping"]["parents"], [None, None])

    def test_false_checkpoint_after_inner_summary_blocks_assembly(self):
        source = (ROOT / "examples/python/nested_product_annotated.py").read_text().replace(
            "        i = i - 1", "        i = i - 1\n        # veripy: prove after_inner: False")
        function = self.parse(source)
        proofs = providers(function, "intro n m _ _ _ _; exact ⟨[.int n, .int m], rfl, rfl⟩",
                           exclude={"checkpoint_after_inner"})
        self.check(function, "FalseAfterInner", proofs + '''
theorem rejected : ¬ generated.VC.checkpoint_after_inner := by
  intro valid
  have outer := valid 1 0 _ (by decide) (by decide) rfl
  have inner := outer
    { pc := map0.header, locals := [some (.int 1), some (.int 0), some (.int 1), some (.int 0), none] }
    rfl 1 0 1 0 none rfl (by decide) rfl rfl rfl (by decide)
  have impossible := inner
    { pc := map1.header, locals := [some (.int 1), some (.int 0), some (.int 1), some (.int 0), some (.int 0)] }
    rfl 1 0 1 0 0 rfl (by decide) rfl rfl rfl rfl
  omega
#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_discover pending from generated
example : pending.report.complete = false := rfl
example : pending.report.obligations[1]!.status = "proved" := rfl
example : pending.report.obligations[10]!.status = "pending" := rfl
/-- error: verification incomplete: 1 unresolved VC(s); no VerifiedArtifact exported -/
#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_verify noArtifact from generated
''')

    def test_pre_loop_hint_is_not_reinterpreted_at_inner_exit(self):
        source = (ROOT / "examples/python/nested_product_annotated.py").read_text()
        source = source.replace("        j = m", "        j = m\n        # veripy: prove initialized: j == old(m)")
        source = source.replace("        i = i - 1", "        i = i - 1\n        # veripy: prove stale: j == old(m)")
        self.check(self.parse(source), "StaleFact", nested_counterexample("checkpoint_stale", 1, 1, 0))

    def test_false_runtime_assertion_inside_inner_loop_is_refuted(self):
        source = (ROOT / "examples/python/nested_product_annotated.py").read_text().replace(
            "            j = j - 1", "            j = j - 1\n            # veripy: name fails\n            assert j < 0")
        self.check(self.parse(source), "FalseAssertion", nested_counterexample("checkpoint_fails", 1, 0, 1))

    def test_partial_correctness_does_not_require_a_measure(self):
        source = SINGLE.replace("# veripy: ensures", "# veripy: mode partial\n# veripy: ensures")
        source = source.replace("    # veripy: decreases n\n", "")
        self.verify(self.parse(source, "countdown"), "Partial", "intro n _; exact ⟨[.int n], rfl, rfl⟩")


if __name__ == "__main__":
    unittest.main()

"""Checkpoint attachment, checked edge mapping, and fail-closed generation."""

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
from veripy_frontend.__main__ import run_lean
from veripy_frontend.emit import emit
from veripy_frontend.source import FrontendError, Parser

EXAMPLE = ROOT / "examples/python/triangular_checkpoints.py"
SOURCE = EXAMPLE.read_text()
BRANCHES = '''# veripy: requires is_int(n) and n >= 0
# veripy: ensures result == 0
def countdown(n):
    # veripy: invariant n >= 0
    # veripy: decreases n
    while n > 0:
        if n > 1:
            n = n - 1
            # veripy: prove left: n >= 1
        else:
            # veripy: prove right_entry: n >= 0
            n = n - 1
            # veripy: prove right: n == 0
        # veripy: prove joined: n >= 0
    return n
'''


class SourceCheckpointTests(unittest.TestCase):
    def parse(self, text=SOURCE, name="triangular"):
        return Parser("checkpoint.py", text.encode()).parse(name)

    def mapping(self, function, extra=""):
        return run_lean(emit(function, "CheckpointSource", mapping_only=True) + extra +
                        "\n#veripy_audit CheckpointSource\n")

    def test_attachment_inventory_and_literal_runtime(self):
        function = self.parse()
        assertion, hint = function.checkpoints
        self.assertEqual([c.kind for c in function.checkpoints], ["assertion", "after"])
        self.assertIs(hint.node, assertion.node)
        self.assertEqual(hint.initialized, {"n", "s"})
        self.assertEqual(ast.unparse(hint.claim), "2 * s + n * (n + 1) == old(n) * (old(n) + 1)")
        bundle = function.bundle()
        self.assertEqual(bundle["checkpoints"]["schemaVersion"], 1)
        self.assertEqual([d["target"]["kind"] for d in bundle["directives"][-2:]], ["assertion", "proof_hint"])
        self.assertEqual(bundle["directives"][-1]["target"]["boundary"], "after")
        self.assertEqual(base64.b64decode(bundle["sourceBytesBase64"]), function.raw)
        self.assertEqual(bundle["artifact"]["code"], list(function.code.co_code))
        runtime = FunctionType(function.code, {})
        for n in range(31):
            self.assertEqual(runtime(n), n * (n + 1) // 2)

    def test_assertion_failure_and_loop_tail_have_distinct_roles(self):
        function = self.parse()
        mapping = self.mapping(function)
        assertion, hint = mapping["checkpoints"]
        instructions = list(dis.get_instructions(function.code))
        failure = next(i.offset for i in instructions if i.opname == "RAISE_VARARGS")
        backedge = next(i for i in instructions if i.opname == "JUMP_BACKWARD")
        self.assertEqual(assertion["failureNodes"], [failure])
        self.assertIn(failure, assertion["nodes"])
        self.assertEqual(hint["boundaryEdges"], [{"sourcePC": backedge.offset, "targetPC": backedge.argval}])
        self.assertNotEqual(assertion["boundaryEdges"], hint["boundaryEdges"])
        self.assertEqual(hint["boundaryEdges"], mapping["loopMapping"]["backedges"])

    def test_branch_hints_do_not_become_shared_pc_facts(self):
        function = self.parse(BRANCHES, "countdown")
        self.assertEqual([c.kind for c in function.checkpoints], ["after", "before", "after", "after"])
        extra = '''
namespace CheckpointSource
-- Dropping just one arm of the joined boundary must invalidate its certificate.
example : (VeriPyAsm.Frontend.Checkpoint.check artifact source admitted.translation.code admitted.stack.heights
    checkpointOrigins[3] { checkpointMaps[3] with boundaryEdges := checkpointMaps[3].boundaryEdges.take 1 }).isOk = false := by decide +kernel
end CheckpointSource
'''
        mapping = self.mapping(function, extra)
        left, right_entry, right, joined = mapping["checkpoints"]
        self.assertEqual(len(left["boundaryEdges"]), 1)
        self.assertEqual(len(right["boundaryEdges"]), 1)
        self.assertEqual(left["boundaryEdges"][0]["targetPC"], right["boundaryEdges"][0]["targetPC"])
        self.assertNotEqual(left["boundaryEdges"], right["boundaryEdges"])
        self.assertCountEqual(joined["boundaryEdges"], left["boundaryEdges"] + right["boundaryEdges"])
        self.assertNotEqual(right_entry["boundaryEdges"], right["boundaryEdges"])

    def test_hint_before_loop_excludes_its_backedges(self):
        function = self.parse(SOURCE.replace("    # veripy: loop sum_loop", "    # veripy: prove initialized: s == 0\n    # veripy: loop sum_loop"))
        mapping = self.mapping(function)
        before = mapping["checkpoints"][0]
        self.assertEqual(before["boundaryEdges"], mapping["loopMapping"]["entryEdges"])
        self.assertNotEqual(before["boundaryEdges"], mapping["loopMapping"]["backedges"])

    def test_elif_and_nested_suite_tails_attach_to_their_own_edges(self):
        source = BRANCHES.replace("        else:\n", "        elif n > 0:\n")
        source = source.replace("        # veripy: prove joined:", "        else:\n            n = n - 1\n            # veripy: prove third: n >= 0\n        # veripy: prove joined:")
        function = self.parse(source, "countdown")
        self.assertEqual([c.label for c in function.checkpoints], ["left", "right_entry", "right", "third", "joined"])
        self.assertEqual(function.checkpoints[-1].node.test.comparators[0].value, 1)
        with self.assertRaisesRegex(FrontendError, "unsupported annotation"):
            self.parse(source.replace("        elif", "        # veripy: prove between_clauses: True\n        elif"), "countdown")
        source = (ROOT / "examples/python/nested_product_annotated.py").read_text()
        source = source.replace("            j = j - 1", "            j = j - 1\n            # veripy: prove inner_done: j >= 0")
        source = source.replace("        i = i - 1", "        # veripy: prove inner_exit: j == 0\n        i = i - 1\n        # veripy: prove outer_done: i >= 0")
        function = self.parse(source, "nested_product")
        self.assertEqual([c.kind for c in function.checkpoints], ["after", "before", "after"])
        mapping = self.mapping(function)
        loops = mapping["loopMapping"]["loops"]
        inner, before, outer = mapping["checkpoints"]
        self.assertEqual(inner["boundaryEdges"], loops[1]["backedges"])
        self.assertEqual(outer["boundaryEdges"], loops[0]["backedges"])
        self.assertNotEqual(before["boundaryEdges"], inner["boundaryEdges"])

    def test_recompilation_keeps_a_hint_before_the_following_assignment(self):
        source = SOURCE.replace("        n = n - 1", "        # veripy: prove before_update: n > 0\n        n = n - 1")
        function = self.parse(source)
        mapping = self.mapping(function)
        boundary = mapping["checkpoints"][0]["entry"]
        statement = function.checkpoints[0].node
        instruction = next(i for i in dis.get_instructions(function.code) if i.offset == boundary)
        self.assertEqual(instruction.positions.lineno, statement.lineno)
        self.assertIn(instruction.opname, ("LOAD_FAST", "LOAD_FAST_BORROW"))
        # Adding a statement changes bytes/offsets; no old offset is reused.
        changed = self.parse(source.replace("        # veripy: prove before_update", "        s = s + 0\n        # veripy: prove before_update"))
        remapped = self.mapping(changed)
        self.assertNotEqual(boundary, remapped["checkpoints"][0]["entry"])
        self.assertNotEqual(function.bundle()["artifactDigest"], changed.bundle()["artifactDigest"])

    def test_assertion_short_circuit_regions_keep_all_passing_exits(self):
        # Put another statement after the assertion, so both passing or-arms
        # reach one actual source statement rather than duplicated backjumps.
        for connective, exit_count in (("and", 1), ("or", 2)):
            with self.subTest(connective=connective):
                text = SOURCE.replace("assert n >= 0", f"assert n >= 0 {connective} n > 10\n        s = s + 0")
                function = self.parse(text)
                assertion = self.mapping(function)["checkpoints"][0]
                self.assertEqual(len(assertion["failureNodes"]), 1)
                self.assertEqual(len(assertion["exitEdges"]), exit_count)
                self.assertEqual(len({edge["targetPC"] for edge in assertion["exitEdges"]}), 1)

    def test_multiline_unicode_and_physical_comment_lines(self):
        source = re.sub(r"\bn\b", "entrée", SOURCE)
        source = source.replace("assert entrée >= 0", "assert (entrée >= 0\n                or entrée > 1)")
        source = source.replace("        # veripy: prove", "        # ordinary\fcomment\u2028continues\n        # veripy: prove")
        for newline in ("\n", "\r\n", "\r"):
            function = self.parse(source.replace("\n", newline))
            self.assertEqual([c.label for c in function.checkpoints], ["remaining_nonnegative", "conserved"])
            inventory = function.bundle()["directives"][-1]
            line = source.split("\n")[inventory["span"]["line"] - 1].encode()
            self.assertEqual(line[inventory["span"]["column"]:inventory["span"]["endColumn"]].decode(), inventory["sourceText"])
        self.mapping(function)

    def test_multiple_hints_and_name_order_preserve_execution_order(self):
        function = self.parse(SOURCE.replace("        assert n >= 0", "        # veripy: prove first: n >= 0\n        # veripy: prove second: n == n\n        assert n >= 0"))
        self.assertEqual([c.label for c in function.checkpoints], ["first", "second", "remaining_nonnegative", "conserved"])
        self.assertIs(function.checkpoints[0].node, function.checkpoints[2].node)
        self.assertEqual(len([d for d in function.directives if d.directive.kind == "prove"]), 3)

    def test_claims_require_initialization_at_their_own_boundary(self):
        for text in (
            SOURCE.replace("    s = 0", "    # veripy: prove premature: s == 0\n    s = 0"),
            SOURCE.replace("assert n >= 0", "assert missing >= 0"),
            SOURCE.replace("prove conserved: 2*s", "prove conserved: 2*missing"),
            SOURCE.replace("    s = 0", "    if n > 0:\n        x = 0\n    # veripy: prove missing_branch: x == 0\n    s = 0"),
        ):
            with self.subTest(text=text), self.assertRaisesRegex(FrontendError, "uninitialized name"):
                self.parse(text)
        function = self.parse(SOURCE.replace("    s = 0", "    s = 0\n    # veripy: prove initialized: s == 0"))
        self.assertIn("s", function.checkpoints[0].initialized)

    def test_duplicate_misplaced_and_unsupported_checkpoints_are_rejected(self):
        for old, new, diagnostic in (
            ("name remaining_nonnegative", "name sum_loop", "duplicate checkpoint label"),
            ("prove conserved:", "prove remaining_nonnegative:", "duplicate checkpoint label"),
            ("name remaining_nonnegative", "name remaining_nonnegative\n        # veripy: name twice", "duplicate name"),
            ("prove conserved:", "prove no_colon", "prove requires"),
            ("        # veripy: prove", "      # veripy: prove", "unsupported annotation"),
            ("assert n >= 0", "assert n >= 0, 'message'", "assertion messages"),
            ("assert n >= 0", "assert old(n) >= 0", "reserved logical name"),
            ("assert n >= 0", "assert is_int(n)", "reserved logical name"),
            ("prove conserved: 2*s", "prove conserved: 2*result", "uninitialized name"),
            ("    return s", "    return s\n    # veripy: prove unreachable: True", "no normal fallthrough"),
            ("    return s", "    # veripy: name misplaced\n    return s", "unsupported annotation"),
            ("        n = n - 1", "        n = n - 1  # veripy: prove inline: True", "unsupported annotation"),
        ):
            with self.subTest(diagnostic=diagnostic), self.assertRaisesRegex(FrontendError, diagnostic):
                self.parse(SOURCE.replace(old, new))

    def test_removed_constant_assertion_and_missing_positions_fail_closed(self):
        function = self.parse(SOURCE.replace("assert n >= 0", "assert True"))
        with self.assertRaisesRegex(FrontendError, "explicit failure site"):
            self.mapping(function)
        function = self.parse()
        bundle = function.bundle()
        assertion_line = function.checkpoints[0].node.lineno
        i = next(i for i, pos in enumerate(bundle["source"]["positions"]) if pos and pos["line"] == assertion_line)
        bundle["source"]["positions"][i] = None
        function.bundle = lambda: bundle
        with self.assertRaisesRegex(FrontendError, "complete instruction positions"):
            self.mapping(function)

    def test_false_claims_are_inspectable_but_never_verified(self):
        function = self.parse(SOURCE.replace("prove conserved: 2*s + n*(n+1) == old(n)*(old(n)+1)", "prove conserved: False"))
        self.assertEqual(ast.unparse(function.checkpoints[-1].claim), "False")
        self.mapping(function)
        with self.assertRaisesRegex(FrontendError, "checkpoint VC generation"):
            emit(function, "FalseHint")
        # A terminal false assertion has a checked failure region and no
        # passing exits. Mapping it does not assume its condition is true.
        source = (ROOT / "examples/python/triangular_annotated.py").read_text().replace("    return s", "    assert False\n    return s")
        function = self.parse(source)
        assertion = self.mapping(function)["checkpoints"][0]
        self.assertEqual(assertion["exitEdges"], [])
        self.assertEqual(len(assertion["failureNodes"]), 1)

    def test_cli_inspection_and_generation_preserve_previous_outputs(self):
        result = subprocess.run([sys.executable, "-m", "veripy_frontend", "inspect", str(EXAMPLE),
                                 "--function", "triangular", "--json"], cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stderr)
        bundle = json.loads(result.stdout)
        self.assertEqual(bundle["status"], "mapping_checked")
        self.assertEqual(len(bundle["mapping"]["checkpoints"]), 2)
        with tempfile.TemporaryDirectory(prefix="veripy-checkpoint-output-") as directory:
            output = Path(directory) / "Generated.lean"
            companion = output.with_suffix(".source.json")
            output.write_text("-- existing module\n")
            companion.write_text("existing companion\n")
            result = subprocess.run([sys.executable, "-m", "veripy_frontend", "generate", str(EXAMPLE),
                                     "--function", "triangular", "--output", str(output)],
                                    cwd=ROOT, text=True, capture_output=True, timeout=180)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("checkpoint VC generation", result.stderr)
            self.assertEqual(output.read_text(), "-- existing module\n")
            self.assertEqual(companion.read_text(), "existing companion\n")


if __name__ == "__main__":
    unittest.main()

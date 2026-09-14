#!/usr/bin/env python3

from contextlib import redirect_stdout
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("lint-style.py")
SPEC = importlib.util.spec_from_file_location("lint_style", SCRIPT)
lint_style = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lint_style)


def numbered_lines(text):
    return list(enumerate(text.splitlines(keepends=True), 1))


class LegacyStyleLinterTest(unittest.TestCase):
    def test_isolated_by_and_colon_ignore_comments(self):
        lines = numbered_lines("/-!\nby\n:e\n-/\n")
        errors, unchanged = lint_style.isolated_by_dot_semicolon_check(lines, Path("Test.lean"))
        self.assertEqual(errors, [])
        self.assertEqual(unchanged, lines)

    def test_isolated_by_and_colon_still_report_code(self):
        lines = numbered_lines("def example : Nat :=\n  by exact 0\n  : Nat\n")
        errors, _ = lint_style.isolated_by_dot_semicolon_check(lines, Path("Test.lean"))
        self.assertEqual(
            [(code, line) for code, line, _ in errors],
            [(lint_style.ERR_IBY, 2), (lint_style.ERR_CLN, 3)],
        )

    def test_left_arrow_ignores_attributes_and_character_literals(self):
        lines = numbered_lines(
            "@[simp ←]\n"
            "attribute [local simp ←] example\n"
            "@[to_dual (attr := grind ←=, grind →)]\n"
            "@[to_additive (attr := simp ←, aesop safe apply)]\n"
            "def arrow := '←'\n"
        )
        errors, unchanged = lint_style.left_arrow_check(lines, Path("Test.lean"))
        self.assertEqual(errors, [])
        self.assertEqual(unchanged, lines)

    def test_left_arrow_checks_code_after_an_attribute(self):
        lines = numbered_lines("@[simp ←] theorem example : True := by rw [←foo]\n")
        errors, fixed = lint_style.left_arrow_check(lines, Path("Test.lean"))
        self.assertEqual([(code, line) for code, line, _ in errors], [(lint_style.ERR_ARR, 1)])
        self.assertEqual(fixed[0][1], "@[simp ←] theorem example : True := by rw [← foo]\n")

    def test_attribute_text_in_a_string_does_not_mask_later_code(self):
        lines = numbered_lines('def text := "@["\nexample := by rw [←foo]\n')
        errors, fixed = lint_style.left_arrow_check(lines, Path("Test.lean"))
        self.assertEqual([(code, line) for code, line, _ in errors], [(lint_style.ERR_ARR, 2)])
        self.assertEqual(fixed[1][1], "example := by rw [← foo]\n")

    def test_left_arrow_reports_missing_operator_space(self):
        lines = numbered_lines("example := by rw [←foo]\nexample := evalTactic (←`(tactic| rfl))\n")
        errors, fixed = lint_style.left_arrow_check(lines, Path("Test.lean"))
        self.assertEqual(
            [(code, line) for code, line, _ in errors],
            [(lint_style.ERR_ARR, 1), (lint_style.ERR_ARR, 2)],
        )
        self.assertEqual(fixed[0][1], "example := by rw [← foo]\n")
        self.assertEqual(fixed[1][1], "example := evalTactic (← `(tactic| rfl))\n")

    def test_fix_preserves_crlf(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Test.lean"
            path.write_bytes(b"example := by\r\n  rw [\xe2\x86\x90foo]\r\n")
            with redirect_stdout(io.StringIO()):
                self.assertEqual(lint_style.main(["--fix", str(path)]), 1)
            self.assertEqual(path.read_bytes(), b"example := by\r\n  rw [\xe2\x86\x90 foo]\r\n")

    def test_obsolete_fixed_column_indentation_is_not_linted(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Test.lean"
            original = "theorem example (h : True) :\n  True := h\n"
            path.write_text(original, encoding="utf8", newline="")
            with redirect_stdout(io.StringIO()):
                self.assertEqual(lint_style.main([str(path)]), 0)
            self.assertEqual(path.read_text(encoding="utf8"), original)


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""
Lint a file or files from mathlib for style.

Sample usage:

    $ ./scripts/lint-style.py Mathlib

which will recursively lint all Lean files in the specified directories. Individual files may also
be passed.

The resulting error output will contain one line for each style error
encountered that isn't in the list of allowed / ignored style exceptions.

Paths with no errors will not appear in the output, and the script will
exit with successful return code if there are no errors encountered in
any provided paths.

Paths emitted in the output will match the paths provided on the
command line for any files containing errors -- in particular, linting
a relative path (like ``Mathlib/Foo/Bar.lean``) will produce errors
that contain the relative path, whilst linting absolute paths (like
``/root/mathlib4/Mathlib/Foo/Bar.lean``) will produce errors with the
absolute path.

The linters in this script are gradually being rewritten in Lean.
Do not add new linters here; please write them in Lean instead.

To run all style linters, run `lake exe lint-style`.
"""

# TODO: This is adapted from the linter for mathlib3. It should be rewritten in Lean.

from pathlib import Path
import sys
import re
import shutil


ERR_IBY = 11 # isolated by
ERR_IWH = 22 # isolated where
ERR_CLN = 16 # line starts with a colon
ERR_ARR = 18 # space after "←"

exceptions = []
new_exceptions = False
output_messages = []


def annotate_comments(enumerate_lines):
    """
    Take a list of tuples of enumerated lines of the form
    (line_number, line, ...)
    and return a list of
    (line_number, line, ..., True/False)
    where lines have True attached when they are in comments.
    """
    nesting_depth = 0 # We're in a comment when `nesting_depth > 0`.
    starts_in_comment = False # Whether we're in a comment when starting the line.
    for line_nr, line, *rem in enumerate_lines:
        # We assume multiline comments do not begin or end within single-line comments.
        if line == "\n" or line.lstrip().startswith("--"):
            yield line_nr, line, *rem, True
            continue
        # We assume that "/-/" and "-/-" never occur outside of "--" comments.
        # We assume that we do not encounter "... -/ <term> /- ...".
        # We also don't account for "/-" and "-/" appearing in strings.
        starts_in_comment = (nesting_depth > 0)
        nesting_depth = nesting_depth + line.count("/-") - line.count("-/")
        in_comment = (starts_in_comment or line.lstrip().startswith("/-")) and \
            (nesting_depth > 0 or line.rstrip().endswith("-/"))
        yield line_nr, line, *rem, in_comment

def annotate_strings(enumerate_lines):
    """
    Take a list of tuples of enumerated lines of the form
    (line_number, line, ...)
    and return a list of
    (line_number, line, ..., True/False)
    where lines have True attached when they are in strings.
    """
    in_string = False
    in_comment = False
    for line_nr, line, *rem in enumerate_lines:
        # ignore comment markers inside string literals
        if not in_string:
            if "/-" in line:
                in_comment = True
            if "-/" in line:
                in_comment = False
        # ignore quotes inside comments
        if not in_comment:
            # crude heuristic: if the number of non-escaped quote signs is odd,
            # we're starting / ending a string literal
            if line.count("\"") - line.count("\\\"") % 2 == 1:
                in_string = not in_string
            # if there are quote signs in this line,
            # a string literal probably begins and / or ends here,
            # so we skip this line
            if line.count("\"") > 0:
                yield line_nr, line, *rem, True
                continue
            if in_string:
                yield line_nr, line, *rem, True
                continue
        yield line_nr, line, *rem, False


def annotate_attribute_syntax(line, nesting_depth):
    """Return positions inside attribute brackets and the depth after this line."""
    protected = set()
    attribute_command = re.match(r"^\s*attribute\b", line)
    command_bracket = line.find("[", attribute_command.end()) if attribute_command else -1
    index = 0
    while index < len(line):
        if nesting_depth == 0:
            if line.startswith("@[", index):
                protected.update((index, index + 1))
                nesting_depth = 1
                index += 2
                continue
            if index == command_bracket:
                protected.add(index)
                nesting_depth = 1
                index += 1
                continue
        else:
            protected.add(index)
            if line[index] == "[":
                nesting_depth += 1
            elif line[index] == "]":
                nesting_depth -= 1
        index += 1
    return protected, nesting_depth


def isolated_by_dot_semicolon_check(lines, path):
    errors = []
    newlines = []
    for line_nr, line, is_comment in annotate_comments(lines):
        if is_comment:
            newlines.append((line_nr, line))
            continue
        if line.strip() == "by":
            # We excuse those "by"s following a comma or ", fun ... =>", since generally hanging "by"s
            # should not be used in the second or later arguments of a tuple/anonymous constructor
            # See https://github.com/leanprover-community/mathlib4/pull/3825#discussion_r1186702599
            prev_line = lines[line_nr - 2][1].rstrip()
            if not prev_line.endswith(",") and not re.search(", fun [^,]* (=>|↦)$", prev_line):
                errors += [(ERR_IBY, line_nr, path)]
        elif line.lstrip().startswith("by "):
            # We also error if the previous line ends on := and the current line starts with "by ".
            prev_line = newlines[-1][1].rstrip()
            if prev_line.endswith(":="):
                # If the previous line is short enough, we can suggest an auto-fix.
                # Future: error also if it is not: currently, mathlib contains about 30 such
                # instances which are not obvious to fix.
                if len(prev_line) <= 97:
                    errors += [(ERR_IBY, line_nr, path)]
                    newlines[-1] = (line_nr - 1, prev_line + " by\n")
                    indent = " " * (len(line) - len(line.lstrip()))
                    line = f"{indent}{line.lstrip()[3:]}"
        elif line.lstrip() == "where":
            errors += [(ERR_IWH, line_nr, path)]
        if line.lstrip().startswith(":"):
            errors += [(ERR_CLN, line_nr, path)]
        newlines.append((line_nr, line))
    return errors, newlines

def left_arrow_check(lines, path):
    errors = []
    newlines = []
    attribute_depth = 0
    for line_nr, line, is_comment, in_string in annotate_strings(annotate_comments(lines)):
        if attribute_depth == 0 and (is_comment or in_string):
            in_attribute = set()
        else:
            in_attribute, attribute_depth = annotate_attribute_syntax(line, attribute_depth)
        if is_comment or in_string:
            newlines.append((line_nr, line))
            continue
        # Allow "←" to be followed by "%" or "`", but not by "`(" or "``(" (since "`()" and
        # "``()" are used for syntax quotations). Ignore arrows in attribute syntax, where the
        # arrow is a direction modifier rather than an operator, and the character literal `'←'`.
        def add_space(match):
            if match.start() in in_attribute:
                return match.group(0)
            if match.start() > 0 and line[match.start() - 1] == "'" and match.group(1) == "'":
                return match.group(0)
            return f"← {match.group(1)}"

        new_line = re.sub(r'←(?:(?=``?\()|(?![%`]))(\S)', add_space, line)
        if new_line != line:
            errors += [(ERR_ARR, line_nr, path)]
        newlines.append((line_nr, new_line))
    return errors, newlines

def output_message(path, line_nr, code, msg):
    # We are outputting for github. We duplicate path, line_nr and code,
    # so that they are also visible in the plaintext output.
    output_messages.append(
        f"::error file={path},line={line_nr},code={code}::{path}:{line_nr} {code}: {msg}")


def format_errors(errors):
    global new_exceptions
    for errno, line_nr, path in errors:
        if (errno, path.resolve(), None) in exceptions:
            continue
        new_exceptions = True
        if errno == ERR_IBY:
            output_message(path, line_nr, "ERR_IBY", "Line is an isolated 'by'")
        if errno == ERR_IWH:
            output_message(path, line_nr, "ERR_IWH", "Line is an isolated where")
        if errno == ERR_CLN:
            output_message(path, line_nr, "ERR_CLN", "Put : and := before line breaks, not after")
        if errno == ERR_ARR:
            output_message(path, line_nr, "ERR_ARR", "Missing space after '←'.")

def lint(path, fix=False):
    global new_exceptions
    with path.open(encoding="utf-8", newline="") as f:
        # We enumerate the lines so that we can report line numbers in the error messages correctly
        # we will modify lines as we go, so we need to keep track of the original line numbers
        lines = f.readlines()
        enum_lines = list(enumerate(lines, 1))
        newlines = enum_lines
        for error_check in [isolated_by_dot_semicolon_check,
                            left_arrow_check]:
            errs, newlines = error_check(newlines, path)
            format_errors(errs)

    # if we haven't been asked to fix errors, or there are no errors or no fixes, we're done
    if fix and new_exceptions and enum_lines != newlines:
        path.with_name(path.name + '.bak').write_text(
            "".join(l for _, l in newlines), encoding="utf8", newline="")
        shutil.move(path.with_name(path.name + '.bak'), path)

def main(argv):
    global new_exceptions, output_messages
    new_exceptions = False
    output_messages = []
    fix = "--fix" in argv
    # The Lean driver diagnoses lint findings from stdout. In that mode, findings should not obscure
    # genuine Python failures by making every nonzero exit code ambiguous.
    allow_lint_errors = "--allow-lint-errors" in argv
    paths_to_lint = (Path(arg) for arg in argv if arg not in {"--fix", "--allow-lint-errors"})

    for path in paths_to_lint:
        paths = sorted(path.rglob("*.lean")) if path.is_dir() else [path]
        for filename in paths:
            lint(filename, fix=fix)

    for message in sorted(output_messages):
        print(message)

    return int(new_exceptions and not allow_lint_errors)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

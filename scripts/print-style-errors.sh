#!/usr/bin/env bash

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

# Print all errors of the python style linter. This script is temporary and should be removed
# once the Python style linters have been rewritten in Lean.
# Humans should use `lake exe lint-style`; this wrapper remains for shell-based tooling.

PYTHONUTF8=1 ./scripts/lint-style.py --allow-lint-errors "$@" Mathlib Archive Counterexamples

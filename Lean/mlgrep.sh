#!/usr/bin/env bash
# grep the Mathlib sources this project builds against: ./mlgrep.sh PATTERN [PATH]
cd "$(dirname "$0")/.lake/packages/mathlib" && grep -rn -- "$1" "${2:-Mathlib}" | head -${N:-40}

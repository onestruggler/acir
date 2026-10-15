#!/usr/bin/env bash
# Check sequentially, with persistent logs and a bounded compacting heap.
set -eu
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
task_repo=$(cd -- "$script_dir/../../../.." && pwd)
cd -- "$task_repo"
development=Examples/Groups/CCX+HH-3qubit
check_logs=local/ccxhh-3qubit-checks
mkdir -p -- "$check_logs"
agda_program=${AGDA:-agda}
agda_heap=${AGDA_HEAP:-3G}
library_options=()
if [[ -f "$script_dir/libraries-wsl" ]]; then
  library_options=("--library-file=$script_dir/libraries-wsl")
fi
check() {
  local relative=$1
  local log_name=${relative//\//-}
  printf 'Checking %s\n' "$relative"
  if "$agda_program" "${library_options[@]}" "$relative" +RTS "-M$agda_heap" -c -RTS \
      > "$check_logs/$log_name.log" 2>&1; then
    printf 'Passed %s\n' "$relative" >> "$check_logs/passed.log"
  else
    tail -n 30 -- "$check_logs/$log_name.log"
    return 1
  fi
}
check "$development/CircuitLemmas.agda"
for part in "$development"/MissingK/Evaluations/E*.agda; do check "$part"; done
check "$development/MissingK.agda"
check "$development/Repaired/Encoding.agda"
check "$development/Repaired/Soundness.agda"
check "$development/Repaired/EncodingMatrices.agda"
for rule in r1a r1b r1c r2a r2b r2c r2d r2e r2f r3a r3b r3c r3d r3e r3f r3g r4a r4b r4c r5a r6a; do
  check "$development/Transport/$rule.agda"
done
check "$development/TwoLevel.agda"
for part in "$development"/FrameEvaluation/E*.agda; do check "$part"; done
for part in "$development"/DecodeMatrices/*.agda; do check "$part"; done
check "$development/Repaired/DecodingMatrices.agda"
check "$development/Repaired/DyadicCompleteness.agda"
for part in "$development"/HadamardRelations/*.agda; do check "$part"; done
check "$development/Repaired/TwoLevelScaled.agda"
check "$development/Repaired/Presentation.agda"
check "$development/Theorems.agda"
check MainTheorems.agda

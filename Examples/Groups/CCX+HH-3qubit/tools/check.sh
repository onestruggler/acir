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
agda_heap=${AGDA_HEAP:-8G}
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
# These seven roots reach every module of the directory.  Theorems
# reaches the transport, the decoding, dyadic completeness, the Hadamard
# relations and the presentation, in one process (peak about 6.5 GB);
# checking their parts as roots of their own only loaded the same
# interfaces again, a process each.
check "$development/CircuitLemmas.agda"
check "$development/MissingK.agda"
check "$development/Theorems.agda"
for audit in FrameChecks RepresentativeChecks StrictMatrix TransportCaseChecks; do
  check "$development/$audit.agda"
done
check MainTheorems.agda

#!/bin/bash
# Check modules in order, each in its own Agda process; stop at the first failure.
#   bash chkall.sh HEAP TIMEOUT mod1.agda mod2.agda ...
heap=$1; to=$2; shift 2
last=$(mktemp)
for f in "$@"; do
  echo "=== $f"
  bash /mnt/d/work2/acir/Examples/Groups/Clifford+CS/scratchpad/stable/chk.sh "$heap" "$to" "$f" | grep -av 'RewritesNothing' | tail -25 > "$last"
  grep -a "maxrss\|exit=" "$last"
  if ! grep -q "exit=0" "$last"; then cat "$last"; exit 1; fi
done
echo ALL-OK

#!/bin/bash
# Check modules in order, each in its own Agda process; stop at the first failure.
#   bash chkall.sh HEAP TIMEOUT mod1.agda mod2.agda ...
heap=$1; to=$2; shift 2
for f in "$@"; do
  echo "=== $f"
  bash /mnt/d/work2/acir/Examples/Groups/Clifford+CS/scratchpad/stable/chk.sh "$heap" "$to" "$f" | grep -av 'RewritesNothing' | tail -25 > "$HOME/chkall-last.txt"
  grep -a "maxrss\|exit=" "$HOME/chkall-last.txt"
  if ! grep -q "exit=0" "$HOME/chkall-last.txt"; then cat "$HOME/chkall-last.txt"; exit 1; fi
done
echo ALL-OK

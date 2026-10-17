#!/bin/bash
# Typecheck one module under the global Agda lock.
#   bash chk.sh HEAP TIMEOUT path/relative/to/repo.agda
heap=$1; to=$2; f=$3
cd /mnt/d/work2/acir || exit 2
out="$HOME/chk-out.txt"
exec 9>"$HOME/.agda-job.lock"
flock 9
start=$(date +%s)
/usr/bin/time -f 'maxrss=%MkB' -o "$HOME/chk-time.txt" timeout "$to" /home/bonest/.local/bin/agda +RTS -M"$heap" -c -RTS "$f" > "$out" 2>&1
rc=$?
grep -av '^ *Loading\|^ *Checking' "$out" | tail -40
cat "$HOME/chk-time.txt"
echo "exit=$rc secs=$(( $(date +%s) - start ))"

#!/bin/bash
# While the build runs: if WSL's available memory falls below 1.2 GB, kill
# the youngest of our Agda jobs (those checking in $PAR5_REPO, default ~/acir-work3), log it.
LOG=${GUARD_LOG:-/tmp/memguard.log}
for i in $(seq 90); do pgrep -f par5x.py > /dev/null && break; sleep 2; done
while pgrep -f par5x.py > /dev/null; do
  a=$(free -m | awk 'NR==2 {print $7}')
  if [ "$a" -lt 1200 ]; then
    p=$(for q in $(pgrep -f '^/usr/bin/agda \+RTS'); do
          [ "$(readlink /proc/$q/cwd)" = "${PAR5_REPO:-$HOME/acir-work3}" ] && echo "$(ps -o etimes= -p $q) $q"
        done | sort -n | head -1 | awk '{print $2}')
    if [ -n "$p" ]; then
      echo "$(date +%T) available ${a} MB: killed $(ps -o args= -p $p | awk '{print $NF}')" >> $LOG
      kill $p
      sleep 20
    fi
  fi
  sleep 3
done
echo "$(date +%T) guard done" >> $LOG

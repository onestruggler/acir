#!/bin/bash
# Regenerate Lemmas/TwoWire.agda, Lemmas/TwoWireMacro.agda and
# TwoQubit/Decoding.agda: build kbc, run the completions, write the Agda.
#
#   bash run.sh [WORKDIR]      (default /tmp/clifford-cs-gen; needs g++ and python3 with numpy)
#
# Each run stops as soon as it has proved all its targets (checked after
# every processed rule, so the result does not depend on the machine's
# speed); SECONDS is only a bound.  Tier 2 runs with both queues, each
# proving all but one of its targets; the Agda takes each target from
# the first run that proves it.
set -e
GEN=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$GEN/../../../../.." && pwd)
WORK=${1:-/tmp/clifford-cs-gen}
mkdir -p "$WORK"
cd "$WORK"
g++ -O2 -std=c++17 -o kbc "$GEN/kbc.cpp"
python3 "$GEN/model.py"

run() {   # run TAG STAGE MAXLEN SECONDS QUEUE [mirror]
  python3 "$GEN/generate.py" input "$2" "$3" "$4" "$5" $6 > "in-$1.txt"
  ./kbc "out-$1.txt" < "in-$1.txt" 2> "err-$1.txt"
  echo "$1: $(grep '^proved' "err-$1.txt" | tail -n 1)"
}

run s0  s0  16 300 small &
run tc  tc  16 300 small &
run s1m s1  16 600 small mirror &
run t2a t2a 16 300 small &
run t2s t2  16 900 small &
run t2f t2  16 900 fifo &
wait

python3 "$GEN/generate.py" agda "$REPO" s0=s0:d tc=tc s1=s1m:m t2a=t2a t2=t2s,t2f

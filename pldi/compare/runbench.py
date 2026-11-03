"""Run the execution benchmark (panel (c) of fig:compare) in WSL.

Both programs decide, for random circuits w of L gates over H, S and CZ on
n wires, that w and w S^4 have the same matrix, each with its own verified
procedure (bench/CliffordBench.agda, Lean/Bench/CliffordBench.lean), on
the same circuits (seeds SEED, ..., SEED + REPS - 1).  Each program times
its decisions itself (monotonic clock), so process start-up is excluded.
Each configuration runs TRIALS times; the median time per decision is kept.
A system stops before the first n at which a decision would take over
LIMIT_MS, extrapolating by a factor GROWTH per wire (8 for Agda's dense
products, 4 for Lean's state vectors).

Usage (in WSL): python3 runbench.py OUT.json
"""
import json, os, statistics, subprocess, sys, time

AGDA = os.path.expanduser('~/agda-bench/CliffordBench')
LEAN = '/mnt/d/work2/acir/Lean/.lake/build/bin/cliffordbench'
L, SEED, REPS, TRIALS = 100, 1, 5, 3
NS = range(2, 11)
LIMIT_MS = 30000

def run(exe, n):
    out = subprocess.run([exe, str(n), str(L), str(SEED), str(REPS)],
                         capture_output=True, text=True, check=True).stdout.split()
    ok, ms = int(out[0]), int(out[1])
    assert ok == REPS, (exe, n, out)
    return ms / REPS

def main():
    res = []
    for name, exe, growth in (('agda', AGDA, 8), ('lean', LEAN, 4)):
        for n in NS:
            trials = [run(exe, n) for _ in range(TRIALS)]
            med = statistics.median(trials)
            res.append(dict(system=name, n=n, L=L, reps=REPS, trials_ms=trials,
                            ms_per_decision=med))
            print(name, n, med, trials, flush=True)
            if med * growth > LIMIT_MS:
                break
    meta = dict(date=time.strftime('%Y-%m-%d'), gates=L, seeds=[SEED, SEED + REPS - 1],
                trials=TRIALS, cpu=open('/proc/cpuinfo').read().split('model name')[1]
                .split('\n')[0].split(':', 1)[1].strip())
    json.dump(dict(meta=meta, results=res), open(sys.argv[1], 'w'), indent=1)

if __name__ == '__main__':
    main()

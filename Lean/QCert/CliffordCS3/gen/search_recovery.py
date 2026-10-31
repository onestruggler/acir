#!/usr/bin/env python3
"""Find syntactic certificates for removing one control of the atom."""
import heapq
import pickle
import random
import sys
import time
from pathlib import Path
import search_white as sw
from three_words import eval_word

ROOT = Path('/tmp/acir-cs3-recovery-search')


def targets():
    def inv(w):
        return sum(((0, 1) if x == 1 else (x,) * 3 for x in reversed(w)), ())
    def comm(a, b):
        return a + b + inv(a) + inv(b)
    d, b, s, k = (2,), (3,), (4,), (1,)
    a = comm(k + d + inv(k), inv(b))
    a0 = comm(k + inv(d) + s + inv(k), inv(b))
    r = comm(k + s + inv(k), inv(b))
    result = [('remove_control', a + a0, r)]
    for _, l, r in result:
        mapping = (0, 2, 7, 8, 5)
        assert eval_word([mapping[x] for x in l]) == eval_word([mapping[x] for x in r])
    return result


def run(seed, seconds=300):
    ROOT.mkdir(exist_ok=True)
    cache = ROOT / 'base.pickle'
    if not cache.exists():
        cache.write_bytes(pickle.dumps(sw.base_rules()))
    base = pickle.loads(cache.read_bytes())
    order = list(range(5))
    random.Random(seed).shuffle(order)
    kb = sw.mod.KB(order, base)
    kb.pending = []
    overlaps = kb.overlaps
    kb.overlaps = lambda a, b: None
    for name, l, r in base:
        kb.process(kb.enc(l), kb.enc(r), ('base', name))
    kb.overlaps = overlaps
    live = list(kb.index.values())
    for a in live:
        for b in live:
            kb.overlaps(a, b)
    ts = targets()
    start = last = time.monotonic()
    solved = {}
    while kb.pending and time.monotonic() - start < seconds:
        m, _, l, r, proof = heapq.heappop(kb.pending)
        if m > 28:
            continue
        kb.process(l, r, proof)
        if time.monotonic() - last > 20:
            for name, l, r in ts:
                nl, sl = kb.reduce(kb.enc(l))
                nr, sr = kb.reduce(kb.enc(r))
                if nl == nr:
                    solved[name] = sl + kb.invert(sr)
            print(seed, len(kb.index), len(kb.pending), list(solved), flush=True)
            last = time.monotonic()
            if solved or len(kb.pending) > 3500000:
                break
    state = dict(letters=order, base=base, rules=kb.rules, solved=solved, targets=ts)
    (ROOT / f'recovery{seed}.pickle').write_bytes(pickle.dumps(state))
    print('FINAL', seed, list(solved), flush=True)


if __name__ == '__main__':
    if sys.argv[1] == 'prepare':
        ROOT.mkdir(exist_ok=True)
        (ROOT / 'base.pickle').write_bytes(pickle.dumps(sw.base_rules()))
        targets()
    else:
        run(int(sys.argv[1]))

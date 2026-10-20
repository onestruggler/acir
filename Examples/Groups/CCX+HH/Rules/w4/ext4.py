#!/usr/bin/env python3
"""Four wires, classical: extra relators that make the point-stabiliser
tower of `tower4.py` close level by level.

    python3 -B ext4.py [half]

Bottom up, level k (letters fixing p1 ... pk) gets the relators among
its own letters: the rule instances, the extras chosen below it, and new
extras, true relators w1·w2⁻¹ with |w1|, |w2| ≤ half (default 3), until
coset enumeration of H_(k+1) closes at the true index.  The new extras
are then thinned greedily.  The extras are written to `ext4.txt`, one
per line, as placed letters."""
import sys
import itertools
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import core as C
import ss
import tower4 as T

LIM = 2_000_000


def name(g):
    l = T.LETTERS[g]
    if l[0] == 'X':
        return f'X{l[1]}'
    if l[0] == 'CX':
        return f'CX{l[1]}>{l[2]}'
    if l[0] == 'CCX':
        return f'CCX{l[1]};{l[2]}{l[3]}'
    return f'SW{l[1]}{l[2]}'


def evaluate(word):
    p = tuple(range(T.D))
    for g in word:
        q = T.PERMS[g]
        p = tuple(q[x] for x in p)
    return p


def candidates(lets, half):
    """w1 reversed(w2) for words of length <= half with equal permutation
    (every letter is an involution, so reversed(w2) = w2⁻¹)."""
    buckets = {}
    layer = [()]
    for _ in range(half):
        nxt = []
        for w in layer:
            for g in lets:
                if not w or w[-1] != g:
                    nxt.append(w + (g,))
        for w in nxt:
            buckets.setdefault(evaluate(w), []).append(w)
        layer = nxt
    out = set()
    for ws in buckets.values():
        ws.sort(key=len)
        for b in ws[1:]:
            r = ws[0] + tuple(reversed(b))
            out.add(r)
    ident = tuple(range(T.D))
    if ident in buckets:
        out |= set(buckets[ident])
    return sorted(out, key=len)


def index(lets, rels, sub):
    pos = {g: i for i, g in enumerate(lets)}
    own = [tuple(pos[g] for g in r) for r in rels if all(g in pos for g in r)]
    return C.index_c(len(lets), own, [(pos[g],) for g in sub], LIM)


def main():
    half = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    base = T.relators_tower()
    chain = T.CHAIN
    levels = []
    for k in range(len(chain) + 1):
        levels.append([g for g in range(len(T.LETTERS)) if all(T.PERMS[g][p] == p for p in chain[:k])])
    levels.append([])        # the bottom level is enumerated over the trivial group
    extras = []
    for k in range(len(levels) - 2, -1, -1):
        lets, nxt = levels[k], levels[k + 1]
        order = ss.order([T.PERMS[g] for g in lets])
        sub = ss.order([T.PERMS[g] for g in nxt]) if nxt else 1
        want = order // sub
        idx = index(lets, base + extras, nxt)
        if idx == want:
            print(f'level {k}: {len(lets)} letters, index {want}, no new extras', flush=True)
            continue
        bs = set(base)
        for h in range(2, half + 1):
            cand = [r for r in candidates(lets, h) if r not in bs]
            idx = index(lets, base + extras + cand, nxt)
            print(f'level {k}: {len(lets)} letters, index {want}; {len(cand)} candidates '
                  f'(words <= {h}) give {idx}', flush=True)
            if idx == want:
                break
        else:
            print('  not enough; raise half')
            break
        # the shortest closing prefix (candidates sorted by length) ...
        lo, hi = 0, len(cand)
        while lo < hi:
            mid = (lo + hi) // 2
            if index(lets, base + extras + cand[:mid], nxt) == want:
                hi = mid
            else:
                lo = mid + 1
        keep = list(cand[:lo])
        print(f'  a prefix of {lo} closes', flush=True)
        # ... thinned: whole chunks first (longest relators first), halving
        # the chunk size, then one at a time
        keep.sort(key=lambda r: (-len(r), r))
        size = max(1, len(keep) // 2)
        while True:
            i = 0
            while i < len(keep):
                trial = keep[:i] + keep[i + size:]
                if trial != keep and index(lets, base + extras + trial, nxt) == want:
                    keep = trial
                else:
                    i += size
            if size == 1:
                break
            size = max(1, size // 2)
        print(f'  kept {len(keep)}:', ['·'.join(name(g) for g in r) for r in keep], flush=True)
        extras += keep
    (HERE / 'ext4.txt').write_text(''.join(' '.join(name(g) for g in r) + '\n' for r in extras))
    print(len(extras), 'extras in all')


if __name__ == '__main__':
    main()

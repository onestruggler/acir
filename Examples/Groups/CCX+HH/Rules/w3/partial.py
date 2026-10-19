"""Derive a three-wire identity from the natural rules by a partial
proof-producing coset enumeration over the two-wire group P2 on the
wires 0, 1.

Labels are elements of P2, kept as canonical words (completeness on two
wires justifies the rewriting); the two-wire relators on the wires 1, 2
are added (completeness on two wires, one wire up).  Cosets along the
target relator are defined first; the enumeration stops at a limit, and
the relator is then traced from coset 0: if it closes there, its label
is trivial and the trace is a derivation.

    python3 -B partial.py "X0 CCX0 X0 CCX0" [limit]
"""
import sys, time
from collections import deque
sys.path.insert(0, '..')
import core as C
import natproof as NP
import proofs as P
import labelled as LB

gs = C.GateSet(3)
rep = C.PermRep(gs)
L = gs.index
LOW = ['X0', 'X1', 'CX0', 'HH0']
HIGH = ['X1', 'X2', 'CX1', 'HH1']

def ev(word):
    return rep.evaluate(word)

def bfs(names):
    letters = [L[n] for n in names]
    best = {ev(()): ()}
    q = deque([()])
    while q:
        w = q.popleft()
        for x in letters:
            w2 = w + (x,)
            k = ev(w2)
            if k not in best:
                best[k] = w2
                q.append(w2)
    return best

CANLOW = bfs(LOW)
CANHIGH = bfs(HIGH)

def schreier(table):
    rels = set()
    for p, w in table.items():
        for x in set(t for t in w) | set(L[n] for n in HIGH):
            r = w + (x,)
            rel = r + tuple(reversed(table[ev(r)]))
            if rel:
                rels.add(rel)
    return rels

# macros: the letters of P2 on the wires 0, 1, by name
MAC = {n: (L[n],) for n in LOW}
BYIDX = {L[n]: n for n in LOW}

class PartialTC(LB.LabelledTC):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.norms = 0

    def join(self, left, right):
        lab = tuple(left) + tuple(right)
        nf = tuple(BYIDX[x] for x in CANLOW[ev(self.dec(lab))])
        if nf == lab:
            return lab, []
        self.norms += 1
        f = self._add(self.dec(lab), self.dec(nf), [(0, ("norm", None), True)])
        return nf, [(0, ("fact", f), True)]

def axioms():
    ax = NP.axioms(gs)
    for k, rel in enumerate(sorted(schreier(CANHIGH))):
        ax.append(P.Axiom(("two12", k), rel, ()))
    return ax

if __name__ == '__main__':
    target = tuple(L[t] for t in sys.argv[1].split())
    assert rep.is_identity(target), 'not an identity'
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 200_000
    seeds = [target[:i] for i in range(1, len(target) + 1)]
    tc = PartialTC(len(gs.names), axioms(), MAC, seed=seeds, limit=limit)
    t0 = time.time()
    try:
        live = tc.run()
        print('enumeration complete:', len(live), 'live')
    except OverflowError:
        print('stopped at', len(tc.rep), 'cosets')
    i, f, lab, st = tc.walk(0, target)
    r = tc.root(f) if i == len(target) else None
    print('trace: letters', i, 'of', len(target), 'ends at', r, 'label', lab,
          'steps', len(st), 'norms', tc.norms, round(time.time() - t0, 1), 's')

def closure(tc, steps):
    seen, stack = set(), [k for (_, (kind, k), _) in steps if kind == 'fact']
    while stack:
        f = stack.pop()
        if f in seen:
            continue
        seen.add(f)
        for (_, (kind, key), _) in tc.facts[f].steps:
            if kind == 'fact':
                stack.append(key)
    return seen

if __name__ == '__main__':
    cl = closure(tc, st)
    norms = sum(1 for f in cl if any(k == 'norm' for (_, (k, _), _) in tc.facts[f].steps))
    print('closure facts', len(cl), 'norm facts', norms,
          'steps', sum(len(tc.facts[f].steps) for f in cl))

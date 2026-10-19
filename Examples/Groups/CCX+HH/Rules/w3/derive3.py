"""Derivations of three-wire identities from the natural rules, with
two-wire steps decided by completeness on two wires.

A state is a word in the gates of Gen 3 (X0 X1 X2 CX0 CX1 CCX0 HH0 HH1).
Moves:
  * a natural three-wire rule, either direction, wherever it fits;
  * a commutation of two adjacent gates on disjoint wires;
  * a two-wire step: a maximal segment of gates on the wires {0, 1}
    (or {1, 2}) is replaced by the canonical word of its element (the
    two-wire group has order 384), which in Agda is completeness on two
    wires (Natural/Width2) applied to the segment.
Bidirectional breadth-first search, with every state kept in two-wire
canonical form.

    python3 -B derive3.py "X0 CCX0" "CCX0 X0"
"""
import sys, time
from collections import deque
sys.path.insert(0, '..')
import core as C
import natproof as NP

gs = C.GateSet(3)
rep = C.PermRep(gs)
L = gs.index
N = gs.names
LOW = {L[n] for n in ('X0', 'X1', 'CX0', 'HH0')}      # wires 0, 1
HIGH = {L[n] for n in ('X1', 'X2', 'CX1', 'HH1')}     # wires 1, 2

def ev(word):
    return rep.evaluate(word)

def bfs_block(letters):
    letters = sorted(letters)
    best = {rep.identity: ()}
    q = deque([rep.identity])
    while q:
        p = q.popleft()
        for x in letters:
            r = tuple(rep.gens[x][i] for i in p)   # p then x: word p ++ [x]
            # evaluate(word ++ [x]) = evaluate(word) after x acts first
            pass
        # use explicit words to be safe
    return None

def canon_table(letters):
    letters = sorted(letters)
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

CAN_LOW = canon_table(LOW)
CAN_HIGH = canon_table(HIGH)
assert len(CAN_LOW) == 384 and len(CAN_HIGH) == 384, (len(CAN_LOW), len(CAN_HIGH))

def normalise(w):
    """Canonical form: split into maximal blocks of LOW or HIGH letters
    (greedy, left to right) and canonicalise each."""
    out = []
    i = 0
    w = list(w)
    while i < len(w):
        x = w[i]
        if x in LOW or x in HIGH:
            S = LOW if x in LOW else HIGH
            if x == L['X1']:
                # X1 belongs to both; extend in whichever block continues
                j = i + 1
                while j < len(w) and w[j] == L['X1']:
                    j += 1
                if j < len(w) and w[j] in HIGH and w[j] not in LOW:
                    S = HIGH
            j = i
            while j < len(w) and w[j] in S:
                j += 1
            blk = tuple(w[i:j])
            can = (CAN_LOW if S is LOW else CAN_HIGH)[ev(blk)]
            out.extend(can)
            i = j
        else:
            out.append(x)
            i += 1
    return tuple(out)

AX = [a for a in NP.axioms(gs) if not (isinstance(a.name, tuple) and a.name[0] in ('inv',))]

def moves(w, maxlen):
    for a in AX:
        for (l, r) in ((a.lhs, a.rhs), (a.rhs, a.lhs)):
            m = len(l)
            if m == 0:
                continue
            for i in range(len(w) - m + 1):
                if w[i:i + m] == l:
                    w2 = w[:i] + r + w[i + m:]
                    if len(w2) <= maxlen:
                        yield normalise(w2)

def find(lhs, rhs, maxlen=24, limit=3_000_000):
    a, b = normalise(lhs), normalise(rhs)
    if a == b:
        return 0
    fa, fb = {a: None}, {b: None}
    qa, qb = deque([a]), deque([b])
    while qa and qb and len(fa) + len(fb) < limit:
        for q, f, g in ((qa, fa, fb), (qb, fb, fa)):
            for _ in range(len(q)):
                w = q.popleft()
                for w2 in moves(w, maxlen):
                    if w2 in f:
                        continue
                    f[w2] = w
                    if w2 in g:
                        return len(fa) + len(fb)
                    q.append(w2)
    return None

def parse(text):
    return tuple(L[t] for t in text.split())

if __name__ == '__main__':
    l, r = parse(sys.argv[1]), parse(sys.argv[2])
    assert ev(l) == ev(r), 'not an identity'
    t0 = time.time()
    res = find(l, r, maxlen=int(sys.argv[3]) if len(sys.argv) > 3 else 24)
    print('found' if res else 'not found', res, round(time.time() - t0, 1), 's')

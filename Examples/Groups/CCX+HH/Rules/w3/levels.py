"""A tower of subgroups for the natural rules on three wires, each level
presented by short relators in its own letters.

    G = W(E8)  >  W(D8)  >  S8  >  AGL(3,2)  >  Z2^3  >  1
    indices       135       128     30         168       8

Letters are words in the gates of Natural (X0 X1 X2 CX0 CX1 CCX0 HH0
HH1); CXr i = HH i CX i HH i is the CNOT from wire i to wire i+1, and
Z1 = HH0 X1 HH0.  At each level the relators are
  * free: every relation of a two-wire subgroup in the level's letters
    (completeness on two wires), and commutations of letters on disjoint
    wires (structural rules);
  * three-wire relators in the level's letters, chosen greedily among
    the short identities until the level's index over the next is right.
The chosen three-wire relators are printed; each must be derived from
the natural rules (partial.py).

    python3 -B levels.py aff|s8|d8 [maxlen]
"""
import sys, itertools, time
from collections import deque
sys.path.insert(0, '..')
import core as C

gs = C.GateSet(3)
rep = C.PermRep(gs)
G = gs.index

def gates(text):
    out = []
    for t in text.split():
        out.append(G[t])
    return tuple(out)

MACRO = {
    'X0': 'X0', 'X1': 'X1', 'X2': 'X2', 'CX0': 'CX0', 'CX1': 'CX1',
    'CXr0': 'HH0 CX0 HH0', 'CXr1': 'HH1 CX1 HH1',
    'CCX0': 'CCX0', 'Z1': 'HH0 X1 HH0', 'HH0': 'HH0', 'HH1': 'HH1',
}
WIRES = {'X0': {0}, 'X1': {1}, 'X2': {2}, 'CX0': {0, 1}, 'CX1': {1, 2},
         'CXr0': {0, 1}, 'CXr1': {1, 2}, 'CCX0': {0, 1, 2}, 'Z1': {1},
         'HH0': {0, 1}, 'HH1': {1, 2}}
# Z1 is spelled on the wires 0, 1, so as a word it is a two-wire letter
# there, but not on the wires 1, 2.
SPELL = dict(WIRES, Z1={0, 1})

LEVELS = {
    'z2': ['X0', 'X1', 'X2'],
    'aff': ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CXr0', 'CXr1'],
    's8': ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CXr0', 'CXr1', 'CCX0'],
    'd8': ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CXr0', 'CXr1', 'CCX0', 'Z1'],
}
BELOW = {'aff': 'z2', 's8': 'aff', 'd8': 's8'}

PERM = {n: rep.evaluate(gates(MACRO[n])) for n in MACRO}

def mul(p, q):
    return tuple(p[i] for i in q)

def ev(word):
    p = rep.identity
    for x in word:
        p = mul(p, PERM[x])
    return p

def bfs(letters):
    best = {rep.identity: ()}
    q = deque([rep.identity])
    while q:
        p = q.popleft()
        for x in letters:
            r = mul(p, PERM[x])
            if r not in best:
                best[r] = best[p] + (x,)
                q.append(r)
    return best

def schreier(letters):
    t = bfs(letters)
    out = set()
    for p, w in t.items():
        for x in letters:
            r = w + (x,) + tuple(reversed(t[mul(p, PERM[x])]))
            out.add(r)
    return out

def free(letters):
    rels = set()
    for wires in ({0, 1}, {1, 2}):
        sub = [x for x in letters if SPELL[x] <= wires]
        if sub:
            rels |= schreier(sub)
    for a, b in itertools.combinations(letters, 2):
        if not (SPELL[a] & SPELL[b]):
            rels.add((a, b, a, b))
    for a in letters:
        rels.add((a, a))
    return rels

def reduced(word):
    return all(word[i] != word[i + 1] for i in range(len(word) - 1)) and word[0] != word[-1]

def spans3(word):
    s = set()
    for x in word:
        s |= WIRES[x]
    return len(s) == 3 and not any(SPELL[x] == {0, 1, 2} for x in [])

def candidates(letters, maxlen, freerels):
    """Short identities spanning the three wires, up to rotation and
    reversal, that are not consequences of nothing (not in freerels)."""
    seen = set()
    out = []
    for n in range(2, maxlen + 1):
        for word in itertools.product(letters, repeat=n):
            if not reduced(word) or ev(word) != rep.identity:
                continue
            ws = set()
            for x in word:
                ws |= SPELL[x]
            if ws != {0, 1, 2}:
                continue
            key = min(min(word[i:] + word[:i], tuple(reversed(word[i:] + word[:i])))
                      for i in range(n))
            if key in seen or key in freerels:
                continue
            seen.add(key)
            out.append(key)
    return out

def index(letters, rels, sub):
    loc = {x: k for k, x in enumerate(letters)}
    r = [tuple(loc[x] for x in w) for w in rels if w]
    s = [(loc[x],) for x in sub]
    return C.index(len(letters), r, s, limit=300_000)

if __name__ == '__main__':
    lev = sys.argv[1]
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    letters, below = LEVELS[lev], LEVELS[BELOW[lev]]
    target = len(bfs(letters)) // len(bfs(below))
    fr = free(letters)
    extra = [tuple(w.split()) for w in sys.argv[3:]]
    print(lev, 'target index', target, 'free relators', len(fr), flush=True)
    print('free alone:', index(letters, list(fr) + extra, below), flush=True)
    cands = candidates(letters, maxlen, fr)
    print('candidates', len(cands), flush=True)
    chosen = list(extra)
    t0 = time.time()
    for c in cands:
        got = index(letters, list(fr) + chosen + [c], below)
        if got is not None:
            chosen.append(c)
            print('  + ', ' '.join(c), '->', got, flush=True)
            if got == target:
                break
    else:
        # keep the candidates that do not overflow but did not finish
        pass
    print('chosen', len(chosen), round(time.time() - t0, 1), 's')
    for c in chosen:
        print('   ', ' '.join(c))

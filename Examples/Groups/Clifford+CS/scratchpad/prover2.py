# A search for derivations of 4-wire identities by 3-wire window steps.
#
# Words are lists of gates (the generators S, K, CS, iI and their
# inverses, the macros X, Z, CX, SWAP, CK, each on given wires).  A step
# replaces a contiguous window whose gates lie on three wires by a word
# with the same operator — one Lemma 5.1 step (SemanticSteps.by-sem,
# Place.lemma-5-1) given completeness on three wires — or commutes two
# adjacent gates on disjoint wires (a structural rule).  Operators are
# compared by fingerprints: the word applied to two fixed random vectors
# over F_p with p = 998244353 (p ≡ 1 mod 4, so i = √−1 exists; the
# gates' entries 1, i, 1/(1+i) live in F_p).
#
# Moves: commute adjacent commuting gates (support ≤ 3), delete a window
# that is the identity, replace a window by the shortest known word with
# its fingerprint (a dictionary built by BFS on each wire triple), and
# pass a gate through its neighbour (g h ↦ h (h⁻¹ g h) with the
# conjugate looked up).  A best-first search from both sides.
import sys, heapq, random
from itertools import combinations
from dec import Dec

P = 998244353
I = pow(3, (P - 1) // 4, P)          # a square root of -1
assert (I * I) % P == P - 1
GINV = pow((1 + I) % P, P - 2, P)    # 1/(1+i)
N = 4
DIM = 1 << N
random.seed(7)
VECS = [[random.randrange(P) for _ in range(DIM)] for _ in range(2)]

def bit(x, w): return (x >> w) & 1

def apply(op, v):
    """the operator of one gate applied to the vector v (a new list)."""
    k = op[0]
    if k == 'iI':  return [(I * a) % P for a in v]
    if k == 'iIi': return [((P - I) * a) % P for a in v]
    if k == 'S':
        w = op[1]; return [(I * a) % P if bit(x, w) else a for x, a in enumerate(v)]
    if k == 'Sd':
        w = op[1]; return [((P - I) * a) % P if bit(x, w) else a for x, a in enumerate(v)]
    if k == 'Z':
        w = op[1]; return [(P - a) % P if bit(x, w) else a for x, a in enumerate(v)]
    if k == 'X':
        w = op[1]; return [v[x ^ (1 << w)] for x in range(DIM)]
    if k in ('K', 'Kd'):
        w = op[1]; out = [0] * DIM
        for x in range(DIM):
            if bit(x, w): continue
            y = x | (1 << w); a, b = v[x], v[y]
            out[x] = (GINV * (a + b)) % P; out[y] = (GINV * (a - b)) % P
        if k == 'Kd': out = [(I * a) % P for a in out]       # K^-1 = i K
        return out
    if k == 'CS':
        a_, b_ = op[1], op[2]; return [(I * c) % P if bit(x, a_) and bit(x, b_) else c for x, c in enumerate(v)]
    if k == 'CSd':
        a_, b_ = op[1], op[2]; return [((P - I) * c) % P if bit(x, a_) and bit(x, b_) else c for x, c in enumerate(v)]
    if k == 'CZ':
        a_, b_ = op[1], op[2]; return [(P - c) % P if bit(x, a_) and bit(x, b_) else c for x, c in enumerate(v)]
    if k == 'CX':
        c_, t = op[1], op[2]; return [v[x ^ (1 << t)] if bit(x, c_) else v[x] for x in range(DIM)]
    if k == 'SWAP':
        a_, b_ = op[1], op[2]
        def sw(x):
            if bit(x, a_) != bit(x, b_): return x ^ (1 << a_) ^ (1 << b_)
            return x
        return [v[sw(x)] for x in range(DIM)]
    if k in ('CK', 'CKd'):
        c_, t = op[1], op[2]; out = list(v)
        for x in range(DIM):
            if not bit(x, c_) or bit(x, t): continue
            y = x | (1 << t); a, b = v[x], v[y]
            out[x] = (GINV * (a + b)) % P; out[y] = (GINV * (a - b)) % P
            if k == 'CKd': out[x] = (I * out[x]) % P; out[y] = (I * out[y]) % P
        return out
    raise ValueError(op)

def fp(word, vecs=VECS):
    """fingerprint: the operator of the word (gates composed in written
    order, the last acting first) on the fixed vectors."""
    out = []
    for v in vecs:
        for op in reversed(word): v = apply(op, v)
        out.extend(v)
    return tuple(out)

FP_ID = fp([])
def support(g): return frozenset(g[1:])

INV = {'iI': 'iIi', 'iIi': 'iI', 'S': 'Sd', 'Sd': 'S', 'K': 'Kd', 'Kd': 'K', 'CS': 'CSd', 'CSd': 'CS',
       'CK': 'CKd', 'CKd': 'CK', 'X': 'X', 'Z': 'Z', 'CZ': 'CZ', 'CX': 'CX', 'SWAP': 'SWAP'}
def ginv(g): return (INV[g[0]],) + g[1:]
def inverse(word): return [ginv(g) for g in reversed(word)]

# ----------------------------------------------------------------------
# The dictionary of shortest words on each triple

def triple_alphabet(T):
    T = sorted(T); out = [('iI',), ('iIi',)]
    for w in T: out += [('S', w), ('Sd', w), ('K', w), ('Kd', w), ('X', w), ('Z', w)]
    for a, b in combinations(T, 2):
        out += [('CS', a, b), ('CSd', a, b), ('CZ', a, b), ('CX', a, b), ('CX', b, a),
                ('CK', a, b), ('CK', b, a), ('CKd', a, b), ('CKd', b, a), ('SWAP', a, b)]
    return out

def better(w1, w2): return (len(w1), w1) < (len(w2), w2)

CANON = {FP_ID: []}
def build_dictionary(maxlen):
    for T in combinations(range(N), 3):
        alpha = triple_alphabet(T)
        frontier = {FP_ID: ([], VECS)}
        for L in range(1, maxlen + 1):
            nxt = {}
            for k, (w, vs) in frontier.items():
                for g in alpha:
                    # operator of w + [g]: g acts first, then w: new vectors = w applied to g(v) ... we keep
                    # the vectors of w applied; instead compute g on the ORIGINAL vectors then w: costly.
                    # So keep words as g applied LAST: build words by prepending.
                    w2 = [g] + w
                    vs2 = [apply(g, v) for v in vs]
                    k2 = tuple(a for v in vs2 for a in v)
                    if k2 in CANON and not better(w2, CANON[k2]): continue
                    CANON[k2] = w2; nxt[k2] = (w2, vs2)
            frontier = nxt
        print(f'  triple {T}: dictionary {len(CANON)} entries', flush=True)

# ----------------------------------------------------------------------
# Moves

def window_fp(word, i, j):
    return fp(word[i:j])

def windows(word):
    """maximal windows [i, j) with support in three wires."""
    out = []
    i = 0
    while i < len(word):
        sup = support(word[i]); j = i + 1
        while j < len(word) and len(sup | support(word[j])) <= 3:
            sup = sup | support(word[j]); j += 1
        out.append((i, j)); i += 1
    return out

def moves(word):
    """all one-step rewrites of the word, each a legal step."""
    out = []
    n = len(word)
    for i in range(n - 1):
        g, h = word[i], word[i + 1]
        if not (support(g) & support(h)):
            out.append((word[:i] + [h, g] + word[i + 2:], ('comm', i)))
        elif len(support(g) | support(h)) <= 3:
            # commute if they commute semantically; pass g through h: g h = h g', g' = h^-1 g h
            k = fp([g, h])
            if k == fp([h, g]):
                out.append((word[:i] + [h, g] + word[i + 2:], ('scomm', i)))
            k2 = fp([ginv(h), g, h])
            if k2 in CANON:
                rep = CANON[k2]
                if len(rep) <= 2:
                    out.append((word[:i] + [h] + rep + word[i + 2:], ('pass', i)))
            k3 = fp([g, h, ginv(g)])
            if k3 in CANON:
                rep = CANON[k3]
                if len(rep) <= 2:
                    out.append((word[:i] + rep + [g] + word[i + 2:], ('pass<', i)))
    # windows canonicalised or deleted
    for (i, j) in windows(word):
        for jj in range(i + 1, j + 1):
            k = fp(word[i:jj])
            if k in CANON and better(CANON[k], word[i:jj]):
                out.append((word[:i] + CANON[k] + word[jj:], ('canon', i, jj)))
    return out

def search(src, dst, budget=20000):
    """best-first search from src to dst by length; both sides are
    canonicalised greedily first."""
    def h(w): return len(w)
    start = tuple(src); goal = tuple(dst)
    seen = {start: None}
    pq = [(h(src), 0, start)]
    cnt = 0
    while pq and cnt < budget:
        _, _, w = heapq.heappop(pq); cnt += 1
        if w == goal: return seen, w
        for w2, mv in moves(list(w)):
            t = tuple(w2)
            if t not in seen:
                seen[t] = (w, mv)
                heapq.heappush(pq, (h(w2), cnt, t))
    return seen, None

def prove(name, lhs, rhs, budget=20000):
    assert fp(lhs) == fp(rhs), name + ': not even semantically equal'
    seen, w = search(lhs, rhs, budget)
    if w is None:
        # try meeting: search from rhs too, into the set seen
        seen2, w2 = search(rhs, lhs, budget)
        common = set(seen) & set(seen2)
        ok = bool(common)
        print(('ok   ' if ok else 'FAIL ') + f'{name} ({len(lhs)} vs {len(rhs)} gates): meet in {len(common)} states' if ok else
              f'FAIL {name}: explored {len(seen)} + {len(seen2)} states, shortest {min(len(s) for s in seen)} / {min(len(s) for s in seen2)}', flush=True)
        return ok
    print(f'ok   {name} ({len(lhs)} vs {len(rhs)} gates)', flush=True)
    return True

if __name__ == '__main__':
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    print('building the dictionary …', flush=True)
    build_dictionary(maxlen)
    D = Dec(N)
    PP0 = D.gadget('pp', 0); PP0f = D.gadget('pp', 0, True); PP1 = D.gadget('pp', 1)
    R0 = D.gadget('rot', 0); R0f = D.gadget('rot', 0, True)
    print('PP0 =', PP0)
    prove('PP0 . PP0flip = eps', PP0 + PP0f, [])
    prove('PP0^4 = eps', PP0 * 4, [])
    prove('PP0 PP1 = PP1 PP0', PP0 + PP1, PP1 + PP0)
    prove('ROT0 . ROT0flip = eps', R0 + R0f, [])
    prove('PP0^2 = ROT0^2', R0 + R0, PP0 + PP0)

# A prover for identities between 4-wire gadget words by 3-wire window
# rewrites.
#
# A step replaces a contiguous window of gates whose support lies in
# three wires by another word with the same matrix: in Agda that is one
# semantic step (SemanticSteps.by-sem, Place.lemma-5-1), justified by
# completeness on three wires.  Commuting two adjacent gates on disjoint
# wires is a structural rule.  So a derivation found here is a
# derivation of the circuit theory on four wires.
#
# Normalisation: windows are canonicalised through a dictionary of the
# shortest words on each wire triple (a BFS over short words, keyed by
# the exact matrix), identity windows are deleted, and disjoint
# neighbours are sorted; two words with the same normal form are equal.
import sys
from itertools import product, combinations
from gadgets import Q, M, ZERO, ONE, I_, MI, NEG, GINV, apply_gate, matrix, check
from dec import Dec, G_pp, G_rot, G_ki, place, layout

N = 4

# ----------------------------------------------------------------------
# Gates: name, wires, and inverses

def support(g):
    return frozenset(g[1:])

INV = {'iI': ('iIi',), 'S': ('Sd',), 'Sd': ('S',), 'K': ('Kd',), 'Kd': ('K',),
       'CS': ('CSd',), 'CSd': ('CS',), 'CK': ('CKd',), 'CKd': ('CK',),
       'X': ('X',), 'Z': ('Z',), 'CX': ('CX',), 'SWAP': ('SWAP',), 'iIi': ('iI',)}

def expand(op):
    """an extended gate as basic gates for apply_gate."""
    k = op[0]
    if k == 'Sd':  return [('S', op[1])] * 3
    if k == 'Kd':  return [('K', op[1]), ('iI',)]
    if k == 'CSd': return [('CS', op[1], op[2])] * 3
    if k == 'CKd': return [('S', op[1]), ('CK', op[1], op[2])]
    if k == 'iIi': return [('iI',)] * 3
    return [op]

def gate_inverse(op):
    k = op[0]
    return (INV[k][0],) + op[1:]

def inverse(word):
    return [gate_inverse(g) for g in reversed(word)]

def mat(word):
    basic = [b for g in word for b in expand(g)]
    return matrix(N, basic)

def key(Mx):
    return tuple(sorted((x, tuple(sorted((y, (v.r, v.i)) for y, v in row.items()))) for x, row in Mx.d.items()))

IDK = key(M.ident(N))

# ----------------------------------------------------------------------
# The canonical dictionary: shortest words on each wire triple

def triple_alphabet(T):
    T = sorted(T)
    out = []
    for w in T:
        out += [('S', w), ('Sd', w), ('K', w), ('Kd', w), ('X', w), ('Z', w)]
    for a, b in combinations(T, 2):
        out += [('CS', a, b), ('CSd', a, b), ('CX', a, b), ('CX', b, a), ('CK', a, b), ('CK', b, a),
                ('CKd', a, b), ('CKd', b, a), ('SWAP', a, b)]
    out += [('iI',), ('iIi',)]
    return out

def better(w1, w2):
    return (len(w1), w1) < (len(w2), w2)

CANON = {}
def build_dictionary(maxlen):
    for T in combinations(range(N), 3):
        alpha = triple_alphabet(T)
        frontier = {IDK: []}
        CANON.setdefault(IDK, [])
        for L in range(1, maxlen + 1):
            nxt = {}
            for k, w in frontier.items():
                Mw = mat(w) if w else M.ident(N)
                for g in alpha:
                    w2 = w + [g]
                    k2 = key(Mw * mat([g]))
                    if k2 in CANON and not better(w2, CANON[k2]): continue
                    if k2 not in CANON or better(w2, CANON[k2]):
                        CANON[k2] = w2
                        nxt[k2] = w2
            frontier = nxt
        print(f'  triple {T}: dictionary {len(CANON)} entries', flush=True)

# ----------------------------------------------------------------------
# Normalisation

def commute_ok(g, h):
    return not (support(g) & support(h))

def gate_order(g):
    return (min(g[1:]) if len(g) > 1 else -1, g)

def normalize(word, trace=None):
    w = list(word)
    changed = True
    while changed:
        changed = False
        # 1. canonicalise maximal 3-wire windows
        i = 0
        while i < len(w):
            sup = support(w[i]); j = i + 1
            while j < len(w) and len(sup | support(w[j])) <= 3:
                sup = sup | support(w[j]); j += 1
            win = w[i:j]
            if len(win) >= 1 and len(sup) >= 1:
                k = key(mat(win))
                if k in CANON and better(CANON[k], win):
                    if trace is not None: trace.append(('win', i, win, CANON[k]))
                    w[i:j] = CANON[k]; changed = True
                    continue
            i += 1
        # 2. sort disjoint neighbours (bubble, one pass)
        for i in range(len(w) - 1):
            g, h = w[i], w[i + 1]
            if commute_ok(g, h) and gate_order(h) < gate_order(g):
                if trace is not None: trace.append(('comm', i, g, h))
                w[i], w[i + 1] = h, g; changed = True
    return w

def prove(name, lhs, rhs):
    nl, nr = normalize(lhs), normalize(rhs)
    ok = nl == nr
    print(('ok   ' if ok else 'FAIL ') + f'{name}: {len(lhs)}->{len(nl)} vs {len(rhs)}->{len(nr)}', flush=True)
    if not ok and len(nl) < 40 and len(nr) < 40:
        print('   nl =', nl); print('   nr =', nr)
    return ok

# ----------------------------------------------------------------------
# The gadgets on four wires, as words of extended gates

def gadget_word(D, kind, a, flip=False):
    """dec.py's placed gadget, with the macro letters kept (X, Z, CX,
    SWAP, CK are atoms here)."""
    return D.gadget(kind, a, flip)

if __name__ == '__main__':
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    print('building the dictionary …', flush=True)
    build_dictionary(maxlen)
    D = Dec(N)
    PP0 = gadget_word(D, 'pp', 0); PP0f = gadget_word(D, 'pp', 0, True)
    PP1 = gadget_word(D, 'pp', 1)
    R0 = gadget_word(D, 'rot', 0); R0f = gadget_word(D, 'rot', 0, True)
    ok = True
    ok &= prove('PP0 . PP0flip = eps', PP0 + PP0f, [])
    ok &= prove('PP0^4 = eps', PP0 * 4, [])
    ok &= prove('PP0 PP1 = PP1 PP0', PP0 + PP1, PP1 + PP0)
    ok &= prove('ROT0 . ROT0flip = eps', R0 + R0f, [])
    ok &= prove('PP0^2 = ROT0^2', PP0 + PP0, R0 + R0)
    print('ALL OK' if ok else 'SOME FAILED')

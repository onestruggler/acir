# Gate-count invariants of the rules: the lattice L spanned by the
# differences of (#S, #K, #CS, #iI) between the two sides of every rule
# (three-wire rules and the two four-wire rules; the structural rules
# change no count).  A true identity whose difference is not in L is not
# derivable.  Checked on the decoded rules of P' at four wires (rules4.py).
import sys, os
sys.path.insert(0, 'four')
from mac import mac_tree, word_of
import deriv

def vec_basic(word):
    v = [0, 0, 0, 0]
    for g, s in word: v[{'S': 0, 'K': 1, 'CS': 2, 'iI': 3}[g]] += 1
    return v

def vec(word):
    """counts of a macro word in the Agda spellings (mac.py)."""
    out = [0, 0, 0, 0]
    for g in deriv.norm(word):
        if g[0] == 'iI' and len(g) == 1: g = ('iI', 0)
        if g[0] == 'iIi' and len(g) == 1: g = ('iIi', 0)
        if g[0] in ('CK', 'CKd', 'CX') and g[1] == g[2]: raise ValueError(g)
        b = vec_basic(word_of(mac_tree(g)))
        out = [a + c for a, c in zip(out, b)]
    return out

def diff(l, r): return [a - b for a, b in zip(vec(l), vec(r))]

R3 = {
 'order-I': ([('iI',)] * 4, []), 'order-S': ([('S', 0)] * 4, []), 'order-K': ([('K', 0)] * 2, [('iI',)] * 3),
 'order-SK': ([('S', 0), ('K', 0)] * 3, [('iI',)] * 3), 'order-CS': ([('CS', 0, 1)] * 4, []),
 'X-CS0': ([('X', 0), ('CS', 0, 1)], [('CS', 0, 1)] * 3 + [('X', 0), ('S', 1)]),
 'rel-267': ([('CX', 1, 0), ('CX', 0, 1)] + [('CS', 1, 2)] * 2 + [('CX', 0, 1), ('CX', 1, 0)],
             [('CX', 0, 1)] + [('CS', 1, 2)] * 2 + [('CX', 0, 1)] + [('CS', 1, 2)] * 2),
}
R4 = {
 'cx-ccz': ([('CX', 3, 2), ('CCZ', 0, 1, 2), ('CX', 3, 2)], [('CCZ', 0, 1, 2), ('CCZ', 0, 1, 3)]),
 'toff-ccz': ([('TOFF', 0, 1, 2), ('CCZ', 0, 1, 3), ('TOFF', 0, 1, 2)], [('CCZ', 0, 1, 3), ('CCZ', 1, 2, 3)]),
}

def hnf(rows):
    """row-style Hermite form over Z (small, by repeated gcd elimination)."""
    rows = [list(r) for r in rows if any(r)]
    out = []; col = 0; n = 4
    while rows and col < n:
        nz = [r for r in rows if r[col] != 0]
        if not nz: col += 1; continue
        while len([r for r in rows if r[col] != 0]) > 1:
            nz = sorted([r for r in rows if r[col] != 0], key=lambda r: abs(r[col]))
            p = nz[0]
            for r in nz[1:]:
                q = r[col] // p[col]
                for k in range(n): r[k] -= q * p[k]
            rows = [r for r in rows if any(r)]
        p = [r for r in rows if r[col] != 0][0]
        if p[col] < 0: p = [-x for x in p]
        out.append(p); rows = [r for r in rows if r is not p and any(r) and r != [-x for x in p]]
        rows = [r for r in rows if r[col] == 0]
        col += 1
    return out

def member(v, basis):
    v = list(v)
    for p in basis:
        c = next(k for k in range(4) if p[k] != 0)
        if v[c] % p[c] != 0: return False
        q = v[c] // p[c]
        v = [a - q * b for a, b in zip(v, p)]
    return not any(v)

if __name__ == '__main__':
    d3 = {k: diff(*v) for k, v in R3.items()}
    d4 = {k: diff(*v) for k, v in R4.items()}
    for k, v in {**d3, **d4}.items(): print(f'{k:10s} {v}')
    B3 = hnf(list(d3.values())); B = hnf(list(d3.values()) + list(d4.values()))
    print('L3 basis', B3); print('L  basis', B)
    det = 1
    for p in B: det *= p[next(k for k in range(4) if p[k] != 0)]
    print('index of L in Z^4:', abs(det) if len(B) == 4 else 'infinite')
    # the decoded rules of P' at four wires
    import rules4

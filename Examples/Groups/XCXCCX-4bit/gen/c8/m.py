"""Model: four-wire {X, CX, CCX} circuits, our wire numbering (wire 0 bottom,
bit w of a state = wire w), words in diagram order (first letter acts first).

Letters: ('X',t), ('CX',c,t), ('CCX',a,b,t) with a>b (black controls).
A permutation is a tuple p with p[x] = image of state x.  Composition in
diagram order: seq(p, q)[x] = q[p[x]].
"""
import itertools

N = 16
LET = []
for t in range(4):
    LET.append(('X', t))
for c in range(4):
    for t in range(4):
        if c != t:
            LET.append(('CX', c, t))
for t in range(4):
    o = sorted((w for w in range(4) if w != t), reverse=True)
    for a, b in itertools.combinations(o, 2):
        LET.append(('CCX', a, b, t))


def act(l, x):
    if l[0] == 'X':
        return x ^ (1 << l[1])
    if l[0] == 'CX':
        return x ^ (((x >> l[1]) & 1) << l[2])
    return x ^ ((((x >> l[1]) & (x >> l[2])) & 1) << l[3])


def lp(l):
    return tuple(act(l, x) for x in range(16))


ID = tuple(range(16))


def seq(p, q):
    """p then q."""
    return tuple(q[p[x]] for x in range(16))


def inv(p):
    r = [0] * 16
    for x in range(16):
        r[p[x]] = x
    return tuple(r)


def wp(word):
    """Permutation of a word (list of letters, or of permutations)."""
    p = ID
    for l in word:
        q = l if isinstance(l, tuple) and len(l) == 16 and all(isinstance(v, int) for v in l) else lp(l)
        p = seq(p, q)
    return p


def cyc(p):
    seen = set()
    out = []
    for x in range(16):
        if x in seen or p[x] == x:
            continue
        c = [x]
        seen.add(x)
        y = p[x]
        while y != x:
            c.append(y)
            seen.add(y)
            y = p[y]
        out.append(tuple(c))
    return out


def sb(x):
    """State as bits w3w2w1w0."""
    return format(x, '04b')


def show(p):
    return ' '.join('(' + ' '.join(sb(v) for v in c) + ')' for c in cyc(p)) or 'id'


def name(l):
    if l[0] == 'X':
        return 'X%d' % l[1]
    if l[0] == 'CX':
        return 'CX%d>%d' % (l[1], l[2])
    return 'CCX%d%d>%d' % (l[1], l[2], l[3])


def wname(w):
    return ' '.join(name(l) for l in w) or 'e'


# Gray order of the lower three wires (w2 w1 w0), as in Width3.enc
GRAY = [0b000, 0b001, 0b011, 0b010, 0b110, 0b111, 0b101, 0b100]


def perm_from_cycles(cycles):
    p = list(range(16))
    for c in cycles:
        for i, x in enumerate(c):
            p[x] = c[(i + 1) % len(c)]
    return tuple(p)


def sign(p):
    s = 1
    for c in cyc(p):
        if len(c) % 2 == 0:
            s = -s
    return s

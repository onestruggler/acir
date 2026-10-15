# The facts of Lemma 8.8 at n = 4 as transports of canonical facts
# (Four/Transport): blocks, frames, and the decoded letters as the
# frame of their position applied to the canonical gadget.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from deriv import Derivation, fp, norm, rename_letter, inv, show
from dec import layout
import gadgetlib as G
from gadgetlib import Gad

PPMID = norm(G.core(0, 1))                                  # TOFF012 CS03 TOFF012 CSd03
RMID = norm(Gad(0, (), ['S', 'K'], -1).letters())           # S0 K0 core^-1 Kd0 Sd0
MID = {'p': PPMID, "p'": PPMID, 'l': RMID, 'h': RMID}
FLIP = {'p': 0, "p'": 1, 'l': 0, 'h': 1}

def tau(j):
    p = {w: w for w in range(4)}; p[j], p[j + 1] = j + 1, j
    return p

# a block: (bits, mid); its letters
def xb(bits): return [('X', w) for w in range(4) if bits[w]]
def flatB(b): return xb(b[0]) + list(b[1]) + xb(b[0])
def flat(bs): return [g for b in bs for g in flatB(b)]

# frame operations, the first the outermost: ('rel', j) or ('col', w)
def step(op, b):
    bits, mid = b
    if op[0] == 'rel':
        t = tau(op[1]); nb = [0] * 4
        for w in range(4):
            if bits[w]: nb[t[w]] = 1
        return (tuple(nb), tuple(rename_letter(g, t) for g in mid))
    w = op[1]
    return (tuple(x ^ (1 if v == w else 0) for v, x in enumerate(bits)), mid)
def TF(ops, bs):
    for op in reversed(ops): bs = [step(op, b) for b in bs]
    return bs

def frame(a, kind):
    """the frame of the decoded letter of `kind` at position a: X on the
    white controls, the shift network, X on the target when oriented."""
    t, x = layout(4, a)
    beta = x[t] ^ FLIP[kind]
    cols = [('col', w) for w in range(4) if w != t and x[w] == 0]
    rels = [('rel', j) for j in range(t - 1, -1, -1)]       # shiftDown t = swapAt (t-1) ... swapAt 0
    return cols + rels + ([('col', 0)] if beta else [])

def decoded(a, kind):
    return TF(frame(a, kind), [((0, 0, 0, 0), tuple(MID[kind]))])[0]

if __name__ == '__main__':
    bad = 0
    for a in range(15):
        for kind in MID:
            b = decoded(a, kind)
            t, x = layout(4, a); beta = x[t] ^ FLIP[kind]
            W = tuple(w for w in range(4) if w != t and x[w] == 0)
            g = Gad(t, W, (G.XW if beta else []) + (['S', 'K'] if kind in 'lh' else []), -1 if kind in 'lh' else 1)
            if fp(norm(flatB(b))) != fp(g.letters()): bad += 1; print('BAD', a, kind)
    print('decoded blocks checked, bad:', bad)

# ------------------------------------------------------------ the instances
# a side is a list of (position offset, kind); offset 0 is the lower position
FIELDS1 = {   # one position
    'p-inv':  ([(0, 'p'), (0, "p'")], []),
    "p'-inv": ([(0, "p'"), (0, 'p')], []),
    'p-ord':  ([(0, 'p')] * 4, []),
    'sq':     ([(0, 'p'), (0, 'p')], [(0, 'l'), (0, 'l')]),
    'l-inv':  ([(0, 'l'), (0, 'h')], []),
    'h-inv':  ([(0, 'h'), (0, 'l')], []),
    'conj2':  ([(0, 'p'), (0, 'l')], [(0, 'l'), (0, "p'")]),
}
FIELDS2 = {   # two positions, the second `d` above the first
    'p-adj':   (1, [(0, 'p'), (1, 'p')], [(1, 'p'), (0, 'p')]),
    'conj-up': (1, [(1, 'p'), (0, 'l')], [(0, 'l'), (0, 'p'), (1, 'p')]),
    'conj-dn': (1, [(0, "p'"), (1, "p'"), (1, 'l')], [(1, 'l'), (0, "p'")]),
    'braid':   (1, [(0, 'l'), (1, 'l'), (0, 'l')], [(1, 'l'), (0, 'l'), (1, 'l')]),
    'far-pl+': (2, [(0, 'p'), (2, 'l')], [(2, 'l'), (0, 'p')]),
    'far-pl-': (2, [(2, 'p'), (0, 'l')], [(0, 'l'), (2, 'p')]),
}

def inv_ops(ops): return list(reversed(ops))

def base_frame(a):
    """X on the white controls and the shift network: the frame of position a without its orientation."""
    t, x = layout(4, a)
    return [('col', w) for w in range(4) if w != t and x[w] == 0] + [('rel', j) for j in range(t - 1, -1, -1)]

def blocks(a, side):
    return [decoded(a + off, kind) for off, kind in side]

def canon_side(a, side):
    """the side's blocks carried back by the frame of position a."""
    F = base_frame(a)
    return [TF(inv_ops(F), [b])[0] for b in blocks(a, side)]

def instances():
    out = []
    for name, (l, r) in FIELDS1.items():
        for a in range(15): out.append((name, a, None, l, r))
    for name, (d, l, r) in FIELDS2.items():
        for a in range(15 - d): out.append((name, a, a + d, l, r))
    for a in range(15):
        for b in range(a + 2, 15):
            out.append(('far-ll', a, b, [(0, 'l'), (b - a, 'l')], [(b - a, 'l'), (0, 'l')]))
    return out

# the permutations of the wires 1 2 3 as words of adjacent swaps (outermost first)
from itertools import permutations
def perm_ops(perm):
    """ops (rel j ...) whose TF renames wire w to perm[w] (perm fixes 0)."""
    target = list(perm); ops = []
    cur = [0, 1, 2, 3]
    # bubble: find swaps s.t. composing them gives perm
    import itertools
    for n in range(0, 6):
        for seq in itertools.product([1, 2], repeat=n):
            m = {w: w for w in range(4)}
            for j in reversed(seq):            # innermost first
                t = tau(j); m = {w: t[m[w]] for w in range(4)}
            if all(m[w] == perm[w] for w in range(4)): return [('rel', j) for j in seq]
    raise ValueError(perm)

PERMS = []
for p in permutations([1, 2, 3]):
    perm = {0: 0, 1: p[0], 2: p[1], 3: p[2]}
    PERMS.append((perm, perm_ops(perm)))

def tgt_of(mid):
    for g in mid:
        if g[0] == 'TOFF': return g[1]
    raise ValueError(mid)

def sem(b):
    """a block up to the spelling of its gadget: its X set, kind and target."""
    bits, mid = b
    kind = 'PP' if len(mid) == 4 else 'R'
    return (bits, kind, tgt_of(mid))

def key(side_blocks):
    return tuple(sem(b) for b in side_blocks)

def classify():
    classes = {}
    for (name, a, b, l, r) in instances():
        L0, R0 = canon_side(a, l), canon_side(a, r)
        best = None
        for perm, ops in PERMS:
            Lt, Rt = TF(ops, L0), TF(ops, R0)
            # the lower position's letters respelled back to the canonical mid
            def resp(side, blk):
                return [(bb[0], tuple(MID[k])) if off == 0 else bb for (off, k), bb in zip(side, blk)]
            k = (name, key(resp(l, Lt)), key(resp(r, Rt)))
            if best is None or k < best[0]: best = (k, perm, ops)
        classes.setdefault(best[0], []).append((name, a, b, best[1], best[2]))
    return classes

if __name__ == '__main__' and 'classes' in sys.argv:
    cl = classify()
    from collections import Counter
    print('classes', len(cl), Counter(k[0] for k in cl))

# ------------------------------------------------------------ the full group
# X on any wire and the adjacent swaps generate 2^4 . 4! transports; each
# element is named by a shortest list of operations.
def group():
    def act(ops):
        b = TF(ops, [((1, 0, 0, 0), ()), ((0, 1, 0, 0), ()), ((0, 0, 1, 0), ()), ((0, 0, 0, 1), ()), ((0, 0, 0, 0), ())])
        return tuple(x[0] for x in b)
    seen = {act([]): []}; frontier = [[]]
    gens = [('rel', j) for j in range(3)] + [('col', w) for w in range(4)]
    while frontier:
        nf = []
        for ops in frontier:
            for g in gens:
                o2 = [g] + ops
                k = act(o2)
                if k not in seen: seen[k] = o2; nf.append(o2)
        frontier = nf
    return list(seen.values())

SYM = {'far-ll', 'p-adj'}

def classify_full():
    Gp = group()
    classes = {}
    for (name, a, b, l, r) in instances():
        L, R = blocks(a, l), blocks(a, r)
        best = None
        for ops in Gp:
            Lt, Rt = TF(ops, L), TF(ops, R)
            cands = [(key(Lt), key(Rt), False)]
            if name in SYM: cands.append((key(Rt), key(Lt), True))
            for kl, kr, sw in cands:
                k = (name, kl, kr)
                if best is None or k < best[0]: best = (k, ops, sw)
        classes.setdefault(best[0], []).append((name, a, b, best[1], best[2]))
    return classes

if __name__ == '__main__' and 'full' in sys.argv:
    cl = classify_full()
    from collections import Counter
    print('group', len(group()), 'classes', len(cl), Counter(k[0] for k in cl))

# ------------------------------------------------------------ canonical blocks and class facts
from deriv import relabel, show, BY_NAME
import passes as P
from passes import L
from blocks import BD
def bstr(bits): return "".join(str(b) for b in bits)
import consec4 as C4

def cmid(kind, t):
    if kind == 'PP': return tuple(norm(G.core(t, 1)))
    return tuple(norm(Gad(t, (), ['S', 'K'], -1).letters()))
assert cmid('PP', 0) == tuple(PPMID) and cmid('R', 0) == tuple(RMID)

def cblock(k): return (k[0], cmid(k[1], k[2]))
def kname(k): return f'{bstr(k[0])}{k[1]}{k[2]}'

def gad_of(k):
    bits, kind, t = k
    W = tuple(w for w in range(4) if w != t and bits[w])
    d = (list(G.XW) if bits[t] else []) + (['S', 'K'] if kind == 'R' else [])
    return Gad(t, W, d, -1 if kind == 'R' else 1)

def b2g(k):
    """flatB of the canonical block -> the gadget's letters (None when equal)."""
    g = gad_of(k); bits, kind, t = k
    lhs = norm(flatB(cblock(k))); rhs = norm(g.letters())
    if lhs == rhs: return None
    name = f'b2g {kname(k)}'
    if name in L: return name
    d = Derivation(name, lhs, rhs, L)
    xs = xb(bits); n = len(xs); m = len(cmid(kind, t))
    if bits[t]:
        i = xs.index(('X', t))
        for j in range(i, n - 1): d.comm(j)                      # X_t innermost on the left
        for j in range(n + m + i - 1, n + m - 1, -1): d.comm(j)  # and on the right
    nW = n - (1 if bits[t] else 0)
    pre = ([('X', t)] if bits[t] else []) + ([('S', t), ('K', t)] if kind == 'R' else [])
    post = ([('Kd', t), ('Sd', t)] if kind == 'R' else []) + ([('X', t)] if bits[t] else [])
    dl = [(x, t) for x in g.d]; dr = [(x, t) for x in G.winv(list(g.d))]
    if pre != dl: d.win(nW, nW + len(pre), dl)
    o = nW + len(dl) + len(G.core(t, g.e))
    if post != dr: d.win(o, o + len(post), dr)
    d.done(); return name

def to_gad(bd, i, k):
    """block i (the canonical spelling of k) -> its gadget spelling."""
    n = b2g(k)
    if n: bd.lem(i, 1, [gad_of(k).letters()], n)
def from_gad(bd, i, k):
    n = b2g(k)
    if n: bd.lem(i, 1, [flatB(cblock(k))], n, fwd=False)

def cls_name(kl, kr):
    return 'cls ' + (' '.join(kname(k) for k in kl) or 'e') + ' = ' + (' '.join(kname(k) for k in kr) or 'e')

Z4 = (0, 0, 0, 0); X0b = (1, 0, 0, 0); X1b = (0, 1, 0, 0)
PI01 = (1, 0, 2, 3)

def rg1(): return relabel(C4.rot_gad(), PI01, L)

def sep_fact(kl, kr):
    """two gadgets separated on a wire commute (sep_pass)."""
    A, B = kl
    assert list(kr) == [B, A]
    c = [w for w in range(4) if w not in (A[2], B[2]) and A[0][w] != B[0][w]][0]
    name = cls_name(kl, kr)
    if name in L: return name
    bd = BD(name, [flatB(cblock(A)), flatB(cblock(B))], flat([cblock(B), cblock(A)]))
    to_gad(bd, 0, A); to_gad(bd, 1, B)
    bd.swap(0, G.sep_pass(gad_of(A), gad_of(B), c))
    from_gad(bd, 0, B); from_gad(bd, 1, A)
    return bd.done()

PINV = "p'-inv"

def recipe(field):
    """(kl, kr, builder) of the consecutive classes, at the configurations of consec4."""
    PPk = lambda b, t: (b, 'PP', t)
    Rk = lambda b, t: (b, 'R', t)
    rg = C4.rot_gad
    def mk(kl, kr, body):
        def build():
            name = cls_name(kl, kr)
            if name in L: return name
            bd = BD(name, [flatB(cblock(k)) for k in kl], flat([cblock(k) for k in kr]))
            body(bd); return bd.done()
        return kl, kr, build
    if field in ('p-inv', PINV):
        def body(bd):
            bd.lem(1, 1, [C4.ai0.letters()], 'PP-flip'); bd.cancel(0)
        return mk([PPk(Z4, 0), PPk(X0b, 0)], [], body)
    if field in ('l-inv', 'h-inv'):
        def body(bd):
            bd.lem(0, 1, [C4.ROT], rg(), fwd=False)
            bd.split(1, [1, len(RMID), 1]); bd.lem(2, 1, [C4.ROT], rg(), fwd=False)
            bd.join(0, 4); bd.lem(0, 1, [[]], 'ROT-inv'); bd.b = []
        return mk([Rk(Z4, 0), Rk(X0b, 0)], [], body)
    if field == 'p-ord':
        def body(bd):
            bd.join(0, 4); bd.lem(0, 1, [[]], 'PP4'); bd.b = []
        return mk([PPk(Z4, 0)] * 4, [], body)
    if field == 'sq':
        def body(bd):
            bd.lem(0, 2, [[C4.E]], 'PP2=E'); bd.lem(0, 1, [C4.ROT, C4.ROT], 'ROT2=E', fwd=False)
            bd.lem(0, 1, [RMID], rg()); bd.lem(1, 1, [RMID], rg())
        return mk([PPk(Z4, 0)] * 2, [Rk(Z4, 0)] * 2, body)
    if field == 'conj2':
        def body(bd):
            bd.lem(1, 1, [C4.ROT], rg(), fwd=False)
            bd.lem(0, 2, [C4.ROT, flatB(cblock(PPk(X0b, 0)))], C4.F6())
            bd.lem(0, 1, [RMID], rg())
        return mk([PPk(Z4, 0), Rk(Z4, 0)], [Rk(Z4, 0), PPk(X0b, 0)], body)
    if field == 'conj-up':
        def body(bd):
            bd.lem(1, 1, [C4.ROT], rg(), fwd=False)
            bd.lem(0, 2, [C4.ROT, PPMID, flatB(cblock(PPk(X1b, 1)))], C4.F7a())
            bd.lem(0, 1, [RMID], rg())
        return mk([PPk(X1b, 1), Rk(Z4, 0)], [Rk(Z4, 0), PPk(Z4, 0), PPk(X1b, 1)], body)
    R1 = list(cmid('R', 1)); ROT1 = list(L[rg1()][0])
    if field == 'conj-dn':
        def body(bd):
            bd.split(2, [1, len(R1), 1]); bd.lem(3, 1, [ROT1], rg1(), fwd=False); bd.join(2, 3)
            bd.lem(0, 3, [bd.b[2], bd.b[0]], C4.F7b())
            bd.split(0, [1, len(ROT1), 1]); bd.lem(1, 1, [R1], rg1()); bd.join(0, 3)
        return mk([PPk(X0b, 0), PPk(Z4, 1), Rk(X1b, 1)], [Rk(X1b, 1), PPk(X0b, 0)], body)
    if field == 'braid':
        def body(bd):
            bd.lem(0, 1, [C4.ROT], rg(), fwd=False); bd.lem(2, 1, [C4.ROT], rg(), fwd=False)
            bd.split(1, [1, len(R1), 1]); bd.lem(2, 1, [ROT1], rg1(), fwd=False); bd.join(1, 3)
            q = bd.b[1]
            bd.lem(0, 3, [q, C4.ROT, q], C4.F10())
            for i in (0, 2):
                bd.split(i, [1, len(ROT1), 1]); bd.lem(i + 1, 1, [R1], rg1()); bd.join(i, 3)
            bd.lem(1, 1, [RMID], rg())
        return mk([Rk(Z4, 0), Rk(X1b, 1), Rk(Z4, 0)], [Rk(X1b, 1), Rk(Z4, 0), Rk(X1b, 1)], body)
    if field == 'p-adj':
        def body(bd):
            bd.lem(1, 1, [C4.ai0.letters()], 'PP-flip')
            bd.swap(0, C4.adj_pass())
            bd.lem(0, 1, [flatB(cblock(PPk(X0b, 0)))], 'PP-flip', fwd=False)
        return mk([PPk(Z4, 1), PPk(X0b, 0)], [PPk(X0b, 0), PPk(Z4, 1)], body)
    return None

GROUP = None

def place(inst, kl, kr):
    """a group element (ops, swapped) carrying the instance to the keys kl = kr."""
    name, a, b, l, r = inst
    Lb, Rb = blocks(a, l), blocks(a, r)
    for ops in GROUP:
        Lt, Rt = TF(ops, Lb), TF(ops, Rb)
        if key(Lt) == tuple(kl) and key(Rt) == tuple(kr): return ops, False
        if name in SYM and key(Rt) == tuple(kl) and key(Lt) == tuple(kr): return ops, True
    return None

def plan():
    """every instance with its group element and its class fact."""
    global GROUP
    GROUP = group()
    out = []; facts = {}
    cl = classify_full()
    rep = {}
    for k, insts in cl.items():
        for (name, a, b, ops, sw) in insts: rep[(name, a, b)] = k
    for inst in instances():
        name, a, b, l, r = inst
        rc = recipe(name)
        if rc:
            kl, kr, build = rc
        else:
            k = rep[(name, a, b)]; kl, kr = list(k[1]), list(k[2])
            build = (lambda kl=kl, kr=kr: sep_fact(kl, kr))
        pl = place(inst, kl, kr)
        if not pl:
            print('NO PLACE', name, a, b, key(blocks(a, l)), key(blocks(a, r))); continue
        fn = cls_name(kl, kr)
        if fn not in facts: facts[fn] = build()
        out.append((inst, pl[0], pl[1], fn, kl, kr))
    return out, facts

if __name__ == '__main__' and 'plan' in sys.argv:
    out, facts = plan()
    print('instances', len(out), 'facts', len(facts))
    for f in facts: print('  ', f, len(BY_NAME[f].d.steps) if hasattr(BY_NAME.get(f), 'd') else (len(BY_NAME[f].steps) if f in BY_NAME else ''))

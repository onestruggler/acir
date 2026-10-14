"""The derivation machinery of a fragment, shared by every spec.

A fragment's spec (cliff.py for Cliff₂, rcliff.py for RCliff₂, ...) fills
in its axioms (axiom), the labels the transcriptions use for them
(LABEL), the equations every search may use (CORE), the symmetry rules
on two and three wires (SWAPS2, SWAPS3), and the Agda modules the
generated module opens (MODULES); derive then finds a chain's steps.

Every equation keeps its two sides as abstract gates (ga, gb) as well as
letters, so that it can be moved to other wires by conjugating with a
swap: the swap passes each spelled gate by a naturality lemma (nat),
and the moved equation comes out in canonical spelling."""
import sys, time
from circ import (Eq, Inst, parse, gparse, spell, permute, gshift, gname, gwires,
                  same, canon, find_steps, agda_list, agda_steps)


LIB = {}
OUT = []            # (name, width, lhs, rhs, steps), in order of definition
MIRROR = {}         # name -> name of its mirror image
NATS = []

LABEL = {}          # a transcription's label -> an equation's name
CORE = []           # the involutions, tried at every step
SWAPS2 = []         # the symmetry rules on two wires
SWAPS3 = []         # ... and on three
NATLABELS = []      # the labels the naturality searches use
MODULES = {}        # 'syntax', 'kit': the Agda modules of the fragment;
                    # 'kitname': the kit as the header names it


def add(e, ga=None, gb=None):
    e.ga, e.gb = ga, gb
    LIB[e.name] = e
    return e


def G(s):
    return gparse(s)


def axiom(name, arity, l, r):
    add(Eq(name, arity, spell(G(l)), spell(G(r))), G(l), G(r))


WIDTH = {0: '', 1: '₁₊', 2: '₂₊', 3: '₃₊', 4: '₄₊'}


def log(*a):
    print(*a, file=sys.stderr, flush=True)


def resolve(labels, width):
    names = []
    for x in labels:
        n = LABEL.get(x, x)
        group = [n] + ([MIRROR[n]] if n in MIRROR else [])
        names += group
        if width >= 3:
            for g in group:
                if LIB[g].arity == 2 and not g.startswith('σ') and not g.startswith('ν'):
                    names.append(outer(g).name)
                    names.append(outer2(g).name)
    return names


def search_lines(name, width, cs, labels_list, depth, extra, maxstates):
    steps = []
    swaps = SWAPS2 + (SWAPS3 if width >= 3 else []) + \
        [m for m in NATS if LIB[m].arity <= width]
    for k in range(1, len(cs)):
        labels = labels_list[k]
        names = list(LIB) if labels is None else resolve(labels, width) + list(extra)
        named = None if labels is None else set(names)
        stages = [(CORE, named), (CORE + swaps, named), (CORE + swaps, None)]
        path = None
        t0 = time.time()
        for st, (more, ins) in enumerate(stages):
            eqs = [LIB[x] for x in dict.fromkeys(names + more) if LIB[x].arity <= width]
            path = find_steps(cs[k - 1], cs[k], eqs, width, depth, maxstates, inserting=ins)
            if path is not None or labels is None:
                break
        log('   %s line %d: %.1fs %s' % (name, k, time.time() - t0,
            'stage %d' % st if path is not None else 'FAIL'))
        if path is None:
            raise SystemExit('%s: no steps found for line %d\n  from %s\n  to   %s'
                             % (name, k, cs[k - 1], cs[k]))
        steps += agda_steps(cs[k - 1], cs[k], path)
    return steps


def derive(name, width, lines, depth=6, extra=(), maxstates=15000, mirror=True):
    """lines: [(text, labels)]; labels name the equations of the step
    leading to that line (None: any equation).  Each step is searched in
    stages: the labels with the involutions, then with the swap rules,
    then allowing every pure insertion."""
    t0 = time.time()
    cs = [parse(t) for t, _ in lines]
    for k, c in enumerate(cs):
        if not same(cs[0], c, width):
            raise SystemExit('%s: line %d is not equal to line 0' % (name, k))
    steps = search_lines(name, width, cs, [l for _, l in lines], depth, extra, maxstates)
    add(Eq(name, width, cs[0], cs[-1]), G(lines[0][0]), G(lines[-1][0]))
    OUT.append((name, width, cs[0], cs[-1], steps))
    if mirror and width == 2 and not name.startswith('σ'):
        add_mirror(name)
    log('-- %s %.1fs' % (name, time.time() - t0))
    return LIB[name]


# ---------------------------------------------------------------------
# Naturality of the swap: SW_k spell(h) = spell(π_k h) SW_k

def pik(k):
    return lambda w: k + 1 if w == k else (k if w == k + 1 else w)


def touches(g, k):
    return bool(gwires(g) & {k, k + 1})


def nat(k, h):
    """The equation SW_k spell(h) = spell(π_k h) SW_k, derived by search."""
    name = 'ν%s%s⁼' % (gname(h), '⁰¹²'[k])
    if name in LIB:
        return LIB[name]
    sk = ('SW', k, k + 1)
    lg, rg = [sk, h], [permute(h, pik(k)), sk]
    l, r = spell(lg), spell(rg)
    ar = max(max(gwires(h)), k + 1) + 1
    labels = list(NATLABELS) + list(NATS)
    labels = [x for x in labels if LABEL.get(x, x) in LIB and LIB[LABEL.get(x, x)].arity <= ar]
    steps = search_lines(name, ar, [l, r], [None, labels], 8, (), 30000)
    add(Eq(name, ar, l, r), lg, rg)
    OUT.append((name, ar, l, r, steps))
    NATS.append(name)
    return LIB[name]


# ---------------------------------------------------------------------
# Conjugation by the swap of wires k, k+1

def conj_steps(e, k, s):
    """σ_k (e lifted by s) σ_k, the swap pushed through gate by gate."""
    ss = LIB['σσ⁼']
    pi = pik(k)
    lg, rg = gshift(e.ga, s), gshift(e.gb, s)
    path = []
    cur = spell([permute(g, pi) for g in lg])

    def rw(ins, i):
        nonlocal cur
        assert cur[i:i + len(ins.l)] == ins.l, (e.name, cur, i, ins.l)
        new = cur[:i] + ins.r + cur[i + len(ins.l):]
        path.append((ins, list(cur), i, new))
        cur = new

    def skip(p, n):                             # SW past a commuting block
        nonlocal cur
        cur = cur[:p] + cur[p + 1:p + 1 + n] + [cur[p]] + cur[p + 1 + n:]
        return p + n

    sk = ('SW', k, k + 1)
    rw(Inst(ss, False, k), 0)                   # SW SW conj(lhs)
    p = 1
    for g in lg:
        h = permute(g, pi)
        if not touches(g, k):
            p = skip(p, len(spell([h])))
        elif g == sk:
            p += 1
        else:                                   # SW spell(h) -> spell(g) SW
            rw(Inst(nat(k, h), True, 0), p)
            p += len(spell([g]))
    rw(Inst(e, True, s), 1)
    p = 0
    for g in rg:
        h = permute(g, pi)
        if not touches(g, k):
            p = skip(p, len(spell([g])))
        elif g == sk:
            p += 1
        else:                                   # SW spell(g) -> spell(h) SW
            rw(Inst(nat(k, g), True, 0), p)
            p += len(spell([h]))
    rw(Inst(ss, True, k), len(cur) - 2)
    assert cur == spell([permute(g, pi) for g in rg])
    return path


def add_conj(name, k, s, newname, width):
    if newname in LIB:
        return LIB[newname]
    e = LIB[name]
    pi = pik(k)
    lg = [permute(g, pi) for g in gshift(e.ga, s)]
    rg = [permute(g, pi) for g in gshift(e.gb, s)]
    l, r = spell(lg), spell(rg)
    path = conj_steps(e, k, s)
    add(Eq(newname, width, l, r), lg, rg)
    OUT.append((newname, width, l, r, agda_steps(l, r, path)))
    return LIB[newname]


def add_mirror(name):
    m = add_conj(name, 0, 0, name[:-1] + '↓⁼', 2)
    MIRROR[name] = m.name
    return m


def outer(name):
    """A two-wire equation on wires 0 and 2 (its wire 1 on wire 2)."""
    return add_conj(name, 0, 1, name[:-1] + 'ᵒ⁼', 3)


def placed(name, seq):
    """A three-wire equation conjugated by the swaps in seq, in turn."""
    cur = name
    for i, k in enumerate(seq):
        nn = name[:-1] + 'ˢ' + ''.join('⁰¹²'[j] for j in seq[:i + 1]) + '⁼'
        cur = add_conj(cur, k, 0, nn, 3).name
    return cur


def emit(d):
    name, width, l, r, steps = d
    ty = 'Eqn n' if width == 0 else 'Eqn (%s n)' % WIDTH[width]
    body = '  (' + '\n   ∷ '.join(steps) + ' ∷ [])' if steps else '  []'
    return '\n'.join(['%s : %s' % (name, ty), '%s = derive' % name,
                      '  ' + agda_list(l), '  ' + agda_list(r), body, '  refl'])


def outer2(name):
    """A two-wire equation on wires 2 and 0 (its wire 0 on wire 2, its
    wire 1 on wire 0)."""
    mid = add_conj(name, 1, 1, name[:-1] + 'ᵗ⁼', 3)
    return add_conj(mid.name, 0, 0, name[:-1] + 'ᵒ′⁼', 3)

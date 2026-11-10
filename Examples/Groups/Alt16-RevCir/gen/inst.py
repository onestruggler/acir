"""From the 24 shapes to the 105 relations between the cycles of Syntactics.

Each cycle Omega_i of Syntactics.agda is a word of letters; as placed
gates it is (T C)^2 for two coloured Toffoli gates, in one of two forms
(the two wires it does not move can be given to T and C either way).
A relation instance follows from the relator of its shape: its cycles
are rewritten as placed gates (omega_def), brought to the forms that the
symmetry carries the shape's to (form_change, from the relator F), and
the shape's relator is transported by the symmetry.
"""
import four as F
from four import M, Proof, LIB, AX, spw, sp, act, inv
import common

bit = common.bit
XL, EL = F.XL, F.EL

KINDS = ('order', 'near', 'far', 'apart')


def omega_letters(i):
    """Syntactics' Omega_i, letter by letter."""
    out = ''
    for n in common.omega_circuit(i):
        if n.startswith('CCX'):
            assert n == 'CCX0'
            out += 'T'
        elif n.startswith('Ex'):
            out += EL[int(n[2:])]
        else:
            assert n[0] == 'X'
            out += XL[int(n[1:])]
    return out


OMEGA = [omega_letters(i) for i in range(14)]
OMEGA_F = [F.func(w) for w in OMEGA]


def forms(i):
    """The two forms of Omega_i as four coloured Toffoli gates: with a, b
    the wires flipped from state i to i + 1 and from i + 1 to i + 2, and
    c < d the other two, T flips b where a is as in state i + 1 and one
    of c, d as in state i, C flips a where b is as in state i + 1 and the
    other one is as in state i.  Form 0 gives c to C."""
    s0, s1, s2 = (common.ENC[i + k] for k in range(3))
    a = (s0 ^ s1).bit_length() - 1
    b = (s1 ^ s2).bit_length() - 1
    c, d = [w for w in range(4) if w not in (a, b)]
    out = []
    for (c1, d1) in ((c, d), (d, c)):
        Tg = M.gate(b, (a, bit(s1, a)), (d1, bit(s0, d1)))
        Cg = M.gate(a, (b, bit(s1, b)), (c1, bit(s0, c1)))
        ws = [w for w in ((Tg, Cg) * 2, (Cg, Tg) * 2) if M.func(w) == OMEGA_F[i]]
        assert len(ws) == 1
        out.append(list(ws[0]))
    return out


FORMS = [forms(i) for i in range(14)]

# K = (Ex0 Ex2 CCX)^4 as placed gates
KG = [M.gate(1, (0, 1), (3, 1)), M.gate(0, (1, 1), (2, 1))] * 2
assert spw(KG) == 'suTusTsuTusT'

SYN = []          # the form of Omega_i that its Syntactics word unfolds to
ODEF = []         # the lemma  letters of Omega_i -> sp(FORMS[i][SYN[i]])


def omega_defs():
    for i in range(14):
        w = OMEGA[i]
        n = (len(w) - 12) // 2
        W = w[:n]
        assert w == W + 'suT' * 4 + F.rev(W)
        pr = Proof(w)
        pr.rw(n + 3, AX['comm-ex2-ex0'].sym())
        pr.rw(n + 9, AX['comm-ex2-ex0'].sym())
        F.unframe_all(pr, 0, W, KG)
        gates = [act(W, g) for g in KG]
        assert gates in FORMS[i], i
        SYN.append(FORMS[i].index(gates))
        ODEF.append(LIB.add('O', pr, spw(gates), 'the cycle %d as placed gates' % i,
                            name='cycle%d' % i))


FCH = []          # sp(FORMS[i][0]) -> sp(FORMS[i][1])


def form_changes(relators):
    d, z = relators['F']
    rel = d['relator']
    assert rel == FORMS[9][0] + FORMS[9][1][::-1]
    pr = F.relator_to_equation(FORMS[9][0], FORMS[9][1], z)
    f9 = LIB.add('F', pr, spw(FORMS[9][1]), 'the two forms of the cycle 9')
    for i in range(14):
        for W in F.HWORDS:
            img = [act(W, g) for g in FORMS[9][0]]
            if img in FORMS[i]:
                break
        else:
            raise AssertionError(i)
        k = FORMS[i].index(img)
        lg, rg, pr = F.transport(f9, FORMS[9][0], FORMS[9][1], W)
        assert lg == FORMS[i][k] and rg == FORMS[i][1 - k]
        eq = LIB.add('F', pr, spw(rg), 'the two forms of the cycle %d' % i)
        FCH.append(eq if k == 0 else eq.sym())


def form_change(i, a, b):
    """sp(FORMS[i][a]) -> sp(FORMS[i][b]), a != b."""
    return FCH[i] if (a, b) == (0, 1) else FCH[i].sym()


def sides(kind, idx):
    """The two sides of a relation as lists of cycles."""
    if kind == 'order':
        (i,) = idx
        return [i, i, i], []
    if kind == 'near':
        i, j = idx
        return [i, j, i], [j, j]
    if kind == 'far':
        i, j, k = idx                 # i, i + 1, i + 2
        return [i, k, i], [k, i, j]
    i, j = idx
    return [j, i], [i, j]


def instances(kind):
    if kind == 'order':
        return [(i,) for i in range(14)]
    if kind == 'near':
        return [(i, i + 1) for i in range(13)]
    if kind == 'far':
        return [(i, i + 1, i + 2) for i in range(12)]
    return [(i, j) for i in range(14) for j in range(i + 3, 14)]


def word(seq, fm):
    out = []
    for i in seq:
        out.extend(FORMS[i][fm[i]])
    return out


def shape_reps(relators):
    """The derived relators by kind: (name, cycles, forms, lemma)."""
    reps = {k: [] for k in KINDS}
    for nm, (d, z) in relators.items():
        if nm == 'order':
            kind, idx, fm = 'order', (9,), {9: 0}
        elif nm.startswith('near'):
            i, j = map(int, nm[4:].split('_'))
            kind, idx, fm = 'near', (i, j), {i: 0, j: 0}
        elif nm.startswith('far'):
            i, k, j = map(int, nm[3:].split('_'))
            kind, idx, fm = 'far', (i, j, k), {i: 0, j: 0, k: 0}
        elif nm.startswith('apart'):
            parts = nm[5:].split('_')
            i, j = int(parts[0]), int(parts[1])
            fi, fj = (int(parts[2][1]), int(parts[2][2])) if len(parts) > 2 else (0, 0)
            kind, idx, fm = 'apart', (i, j), {i: fi, j: fj}
        else:
            continue
        l, r = sides(kind, idx)
        assert d['relator'] == word(l, fm) + word(r, fm)[::-1], nm
        reps[kind].append((nm, idx, fm, z))
    return reps


def instance(kind, idx, reps):
    """The relation between the letters of the cycles, as a lemma."""
    for nm, idx0, fm0, z in reps[kind]:
        l0, r0 = sides(kind, idx0)
        rel0 = word(l0, fm0) + word(r0, fm0)[::-1]
        for W in F.HWORDS:
            fm = {}
            for i0, i in zip(idx0, idx):
                img = [act(W, g) for g in FORMS[i0][fm0[i0]]]
                if img not in FORMS[i]:
                    break
                fm[i] = FORMS[i].index(img)
            else:
                break
        else:
            continue
        break
    else:
        raise AssertionError((kind, idx))
    l, r = sides(kind, idx)
    lw, rw_ = word(l, fm), word(r, fm)
    name = kind + '-' + '-'.join(map(str, idx))
    if W:
        lg, rg, pr = F.transport(z, rel0, [], W)
        assert lg == lw + rw_[::-1]
        zi = LIB.add('Z', pr, '', 'relator of %s, from %s' % (name, nm))
    else:
        zi = z
    pr = Proof(''.join(OMEGA[i] for i in l))
    off = 0
    for i in l:
        pr.rw(off, ODEF[i])
        if fm[i] != SYN[i]:
            pr.rw(off, form_change(i, SYN[i], fm[i]))
        off += len(spw(FORMS[i][fm[i]]))
    assert pr.cur == spw(lw)
    n = len(pr.cur)
    for g in reversed(rw_):
        pr.rw(n, inv(g).sym())
        n += len(sp(g))
    pr.rw(0, zi)
    assert pr.cur == spw(rw_)
    off = 0
    for i in r:
        if fm[i] != SYN[i]:
            pr.rw(off, form_change(i, fm[i], SYN[i]))
        pr.rw(off, ODEF[i].sym())
        off += len(OMEGA[i])
    rhs = ''.join(OMEGA[i] for i in r)
    return LIB.add('N', pr, rhs, name + ', between the cycles of Syntactics', name=name)


def all_instances(relators):
    omega_defs()
    form_changes(relators)
    reps = shape_reps(relators)
    out = {}
    for kind in KINDS:
        for idx in instances(kind):
            out[(kind, idx)] = instance(kind, idx, reps)
    return out

"""Every two-level relation instance on four indices, decoded, derived in
CliffCS₂ on two wires.

An instance is moved into the frame F of one of its pairs (cs2.FRAME):
each generator's decoding is carried, one permutation gate of F at a
time, to F's conjugate of the decoding of its relabelled generator (the
single-gate transports T1…), the frames between the factors cancel, the
canonical instance (w2canon, w2cross, w2swap) applies, and the way back
is the same in reverse.  Each decoded relation is stated on the decoded
letters exactly, so that the Agda decoding produces its sides."""
import w2swap
from twoq import T, C3
from appendixE import OUT, LIB
import circ
from circ import parse, same, find_steps
from cs2 import R, FRAME, IFRAME, conj, CK01, DI, DX, DK, dec

first = len(OUT)
GENS = [('i', a) for a in range(4)] + [('X',) + p for p in FRAME] + [('K',) + p for p in FRAME]
INV = {'X0': 'XX⁼', 'X1': 'XX⁼', 'SW01': 'σσ⁼', 'CX01': 'CXCX↓⁼', 'CX10': 'CXCX⁼'}


def Dg(g):
    return DI[g[1]] if g[0] == 'i' else (DX if g[0] == 'X' else DK)[(g[1], g[2])]


def gname(g):
    return g[0] + ''.join(map(str, g[1:]))


_rel = {}


def relabel(F, g):
    key = (tuple(F), g)
    if key not in _rel:
        _rel[key] = next((h for h in GENS if same(parse(conj(F, Dg(h))), parse(Dg(g)), 2)), None)
    return _rel[key]


# ---------------------------------------------------------------------
# Single-gate transports: D(g) = f D(h) f.

PERM = ['XX⁼', 'σσ⁼', 'CXCX↓⁼', 'CXCX⁼', 'νX0⁼', 'νX1⁼', 'νCX⁼', 'νCX′⁼', 'DX⁼', 'XtCX⁼',
        'XtCX↓⁼', 'XcCX⁼', 'XcCX↓⁼', 'CX3⁼', 'CX3′⁼', 'Nc⁼', 'CSr⁼', 'σCS′⁼', 'XD0⁼', 'XD1⁼',
        'E2⁼', 'E3⁼', 'E4⁼', 'CXCS⁼']
HAND = {
    ('CX01', ('K', 0, 1)): lambda g, h: [
        (Dg(g), None), ('CX01 CX01 ' + Dg(g), ['CXCX↓⁼']), ('CX01 ' + Dg(g) + ' CX01', ['K01CX⁼'])],
    ('CX01', ('K', 0, 2)): lambda g, h: [
        (Dg(g), None), ('X1 CX01 CX01 SW01 ' + CK01 + ' SW01 CX01 CX01 X1', ['CXCX↓⁼']),
        ('CX01 ' + Dg(h) + ' CX01', ['XtCX⁼'])],
    ('CX01', ('X', 0, 2)): lambda g, h: [
        (Dg(g), None), ('X1 CX01 CX01 SW01 CX01 SW01 CX01 CX01 X1', ['CXCX↓⁼']),
        ('CX01 ' + Dg(h) + ' CX01', ['XtCX⁼'])],
    ('CX01', ('i', 0)): lambda g, h: [
        (Dg(g), None), ('CX01 CX01 ' + Dg(g), ['CXCX↓⁼']), ('CX01 ' + Dg(g) + ' CX01', ['CiX0⁼'])],
    ('SW01', ('i', 0)): lambda g, h: [
        (Dg(g), None), ('X0 X1 SW01 CS01 SW01 X1 X0', ['CSr']),
        ('SW01 X1 X0 CS01 X0 X1 SW01', ['νX0⁼', 'νX1⁼']), ('SW01 ' + Dg(h) + ' SW01', [])],
    ('SW01', ('X', 0, 3)): lambda g, h: [
        (Dg(g), None), ('SW01 X0 X1', ['X03s⁼']), ('X0 X1 SW01', ['νX0⁼', 'νX1⁼']),
        ('SW01 SW01 X0 X1 SW01', ['σσ⁼']), ('SW01 ' + Dg(h) + ' SW01', ['X03s⁼'])],
    ('SW01', ('K', 0, 3)): lambda g, h: [
        (Dg(g), None), ('CX10 X0 ' + CK01 + ' X0 CX10', ['FE03⁼']),
        ('X0 CX10 ' + CK01 + ' CX10 X0', ['XtCX↓⁼']),
        ('X0 SW01 CX01 SW01 ' + CK01 + ' SW01 CX01 SW01 X0', ['X13s⁼']),
        ('SW01 ' + Dg(h) + ' SW01', ['νX0⁼'])],
}

# The controlled K on x₀ = 0 passes the CNOT from wire 0.
B = 'S1 ' + C3
TB = 'H1 ' + B + ' H1'
T('TBCX⁼', 2, [(TB + ' CX01', None), (TB + ' H1 CS01 H1 H1 CS01 H1', ['H2']),
               ('H1 CS01 H1 H1 CS01 H1 ' + TB, ['tBt⁼']), ('CX01 ' + TB, ['H2'])])
T('K01CX⁼', 2, [(DK[(0, 1)] + ' CX01', None),
                (B + ' ' + TB + ' ' + B + ' w6 S0 CX01', ['K01W⁼']),
                ('CX01 ' + B + ' ' + TB + ' ' + B + ' w6 S0', ['A2B⁼', 'TBCX⁼', 'S0CX⁼']),
                ('CX01 ' + DK[(0, 1)], ['K01W⁼'])], maxstates=40000)

# Lemma 19: S on wire 1 is i₁ i₃.
T('i1i3⁼', 2, [(DI[1] + ' CS01', None), (C3 + ' S1 CS01', ['XD0⁼']), ('S1', ['E3⁼', 'E2⁼'])])

T1 = {}


def t1(f, g):
    """The name of the lemma D(g) = f D(h) f, deriving it on first use."""
    h = relabel([f], g)
    if Dg(g) == conj([f], Dg(h)):
        return None, h
    name = 'T' + f + gname(g) + '⁼'
    if name not in LIB:
        if (f, g) in HAND:
            T(name, 2, HAND[(f, g)](g, h), maxstates=40000)
        else:
            T(name, 2, [(Dg(g), None), (conj([f], Dg(h)), PERM)], maxstates=40000)
    return name, h


def transport_lines(F, g, prefix, suffix):
    """Lines carrying the factor D(g), between prefix and suffix, to
    conj(F, D(g′)); returns them and g′."""
    lines = []
    hF = relabel(F, g)
    if Dg(g) == conj(F, Dg(hF)):
        return lines, hF
    cur = g
    for m in range(1, len(F) + 1):
        name, h = t1(F[m - 1], cur)
        if name is not None:
            lines.append((' '.join(x for x in [prefix, conj(F[:m], Dg(h)), suffix] if x), [name]))
        cur = h
    assert cur == hF, (F, g, cur, hF)
    return lines, hF


def cancel_lines(F, parts):
    """parts: the factors Y_i of conj(F, Y_1) … conj(F, Y_n); lines merging
    them into conj(F, Y_1 … Y_n), one cancelled pair of gates a line."""
    lines = []
    ys = list(parts)
    while len(ys) > 1:
        a, b = ys[0], ys[1]
        rest = ys[2:]
        for j in range(1, len(F) + 1):
            mid = ' '.join(x for x in [a] + list(reversed(F[j:])) + F[j:] + [b] if x)
            full = ' '.join(x for x in [conj(F, mid)] + [conj(F, y) for y in rest] if x)
            lines.append((full, [INV[F[j - 1]]]))
        ys = [' '.join(x for x in [a, b] if x)] + rest
    return lines, ys[0] if ys else ''


CANON = {}


def canon_name(fam, lt, rt):
    key = (fam, tuple(map(gname, lt)), tuple(map(gname, rt)))
    table = {
        ('order-i', ('i3',) * 4, ()): 'E2⁼', ('order-X', ('X23', 'X23'), ()): 'CXCX↓⁼',
        ('order-K', ('K23',) * 8, ()): 'CK8⁼',
        ('rel-13', ('K23', 'i3', 'i3'), ('X23', 'K23')): 'C13⁼',
        ('rel-14', ('K23', 'i3', 'i3', 'i3'), ('i3', 'K23', 'i3', 'K23')): 'C14⁼',
        ('rel-15', ('K23', 'i2', 'i3'), ('i2', 'i3', 'K23')): 'C15⁼',
        ('rel-16', ('K23', 'K23', 'i2', 'i3'), ()): 'C16⁼',
        ('swap-iX', ('i3', 'X23'), ('X23', 'i2')): 'C10⁼',
        ('comm-ii', ('i0', 'i3'), ('i3', 'i0')): 'Cii0⁼', ('comm-ii', ('i1', 'i3'), ('i3', 'i1')): 'Cii1⁼',
        ('comm-ii', ('i2', 'i3'), ('i3', 'i2')): 'Cii2⁼',
        ('comm-iX', ('i0', 'X23'), ('X23', 'i0')): 'CiX0⁼', ('comm-iX', ('i1', 'X23'), ('X23', 'i1')): 'CiX1⁼',
        ('comm-iK', ('i0', 'K23'), ('K23', 'i0')): 'CiK0⁼', ('comm-iK', ('i1', 'K23'), ('K23', 'i1')): 'CiK1⁼',
        ('comm-XX', ('X01', 'X23'), ('X23', 'X01')): 'CXX⁼', ('comm-XK', ('X01', 'K23'), ('K23', 'X01')): 'CXK⁼',
        ('comm-KK', ('K01', 'K23'), ('K23', 'K01')): 'CKK⁼',
        ('rel-17', ('K01', 'K23', 'K02', 'K13'), ('K02', 'K13', 'K01', 'K23')): 'R17a⁼',
        ('rel-17', ('K02', 'K13', 'K01', 'K23'), ('K01', 'K23', 'K02', 'K13')): 'R17b⁼',
        ('swap-KX', ('K23', 'X02'), ('X02', 'K03')): 'SKXb⁼', ('swap-KX', ('K23', 'X12'), ('X12', 'K13')): 'SKXa⁼',
        ('swap-KX′', ('K03', 'X23'), ('X23', 'K02')): 'SKXb′⁼', ('swap-KX′', ('K13', 'X23'), ('X23', 'K12')): 'SKXa′⁼',
        ('swap-XX', ('X23', 'X02'), ('X02', 'X03')): 'SXXb⁼', ('swap-XX', ('X23', 'X12'), ('X12', 'X13')): 'SXXa⁼',
        ('swap-XX′', ('X03', 'X23'), ('X23', 'X02')): 'SXXb′⁼', ('swap-XX′', ('X13', 'X23'), ('X23', 'X12')): 'SXXa′⁼',
    }
    return table[key]


def frame_of(fam, idx):
    if fam in ('order-X', 'order-K', 'rel-13', 'rel-14', 'rel-15', 'rel-16', 'swap-iX'):
        return FRAME[(int(idx[0]), int(idx[1]))]
    if fam == 'order-i':
        return IFRAME[int(idx)]
    if fam == 'comm-ii':
        return IFRAME[int(idx.split()[1])]
    if fam in ('comm-iX', 'comm-iK'):
        kl = idx.split()[1]
        return FRAME[(int(kl[0]), int(kl[1]))]
    if fam in ('comm-XX', 'comm-XK', 'comm-KK'):
        a, b = idx.split()
        return FRAME[(int(b[0]), int(b[1]))]
    if fam.startswith('swap-'):
        j, k, l = map(int, idx)
        return FRAME[(k, l)]
    return []


NAME = {k: 'W' + k.replace(' ', '-') + '⁼' for k in R}


def instance_lines(key, l, r):
    fam, idx = key.split(' ', 1)
    F = frame_of(fam, idx)
    lines = [(dec(l), None)]

    def carry(word):
        """Lines from dec(word) to the frame form, and the relabelled word."""
        out, gs = [], []
        texts = [Dg(g) for g in word]
        for k, g in enumerate(word):
            pre = ' '.join(texts[:k])
            suf = ' '.join(texts[k + 1:])
            ls, h = transport_lines(F, g, pre, suf)
            out += ls
            texts[k] = conj(F, Dg(h))
            gs.append(h)
        return out, gs, texts

    ll, lt, ltexts = carry(l)
    lines += ll
    cl, lmid = cancel_lines(F, [Dg(h) for h in lt])
    lines += cl
    rl, rt, rtexts = carry(r)
    cr, rmid = cancel_lines(F, [Dg(h) for h in rt])
    name = canon_name(fam, lt, rt)
    canon_line = conj(F, rmid) if rmid else ' '.join(F + list(reversed(F)))
    lines.append((canon_line, [name]))
    if not rmid:
        # F F̄ cancels to nothing
        cur = list(F) + list(reversed(F))
        while cur:
            k = len(cur) // 2
            g = cur[k - 1]
            cur = cur[:k - 1] + cur[k + 1:]
            lines.append((' '.join(cur), [INV[g]]))
        return lines
    back = [(t, None) for t, _ in reversed([(dec(r), None)] + rl + cr)]
    # the way back: each line of the right side's chain, in reverse,
    # with the label of the step it undoes
    fwd = [(dec(r), None)] + rl + cr
    for k in range(len(fwd) - 1, 0, -1):
        lines.append((fwd[k - 1][0], fwd[k][1]))
    return lines


done = 0
for key, (l, r) in R.items():
    lines = instance_lines(key, l, r)
    # drop repeated lines
    clean = [lines[0]]
    for t, lab in lines[1:]:
        if t != clean[-1][0]:
            clean.append((t, lab))
    T(NAME[key], 2, clean, maxstates=40000)
    done += 1

del OUT[:first]

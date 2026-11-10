#!/usr/bin/env python3
"""Draw the canonical-circuit figure of Section 6 (fig:xcxccx-canon) and
check the example of that section.

Writes, next to this file and in the style of rule-*.tex,

  canon-cycle-word.tex    the cycle Omega_9 = (sigma_0 sigma_2 CCX)^4
  canon-cycle-form.tex    the same cycle as a commutator of two Toffolis
  canon-toffoli-gate.tex  the Toffoli gate CCX (controls 2 1, target 0)
  canon-toffoli-form.tex  its canonical circuit Omega_9 ... Omega_4, each
                          cycle as a commutator of two Toffoli gates

Every drawn circuit is evaluated on the sixteen states before anything is
written, and so are the numbers that the text quotes.  Python 3, no
dependencies:  python draw_canon.py

Conventions, as in the paper and in Examples/Groups/Alt16-RevCir: wire 0
is the bottom wire, a state is the bit string b3 b2 b1 b0, circuits are in
diagram order (the left factor is applied first), and position i is the
state with the binary digits of i xor (i >> 1).  A permutation p is a
tuple with p[x] the image of x, and mul(p, q) applies p and then q.
"""
from pathlib import Path

OUT = Path(__file__).resolve().parent
N = 16
GRAY = [i ^ (i >> 1) for i in range(N)]            # position -> state
POS = {s: i for i, s in enumerate(GRAY)}            # state -> position


# ---------------------------------------------------------------------
# Gates.  ('X', t, controls) is a NOT on wire t with controls, a tuple of
# (wire, value) pairs; ('SW', d) swaps the wires d and d + 1.

def X(t, *controls):
    return ('X', t, tuple(sorted(controls, reverse=True)))


def SW(d):
    return ('SW', d)


def apply(g, s):
    if g[0] == 'X':
        _, t, cs = g
        return s ^ (1 << t) if all((s >> c) & 1 == v for c, v in cs) else s
    _, d = g
    a, b = (s >> d) & 1, (s >> (d + 1)) & 1
    return s ^ (1 << d) ^ (1 << (d + 1)) if a != b else s


def perm(word):
    """The permutation of the positions that a circuit carries out."""
    out = []
    for i in range(N):
        s = GRAY[i]
        for g in word:
            s = apply(g, s)
        out.append(POS[s])
    return tuple(out)


IDENT = tuple(range(N))


def mul(p, q):
    return tuple(q[p[i]] for i in range(N))


def inv(p):
    r = [0] * N
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def omega(i):
    """Lafont's cycle of the points i, i + 1, i + 2."""
    p = list(range(N))
    p[i], p[i + 1], p[i + 2] = i + 1, i + 2, i
    return tuple(p)


# ---------------------------------------------------------------------
# The cycles Omega_0 .. Omega_13, as Syntactics.agda defines them.

CCX = X(0, (2, 1), (1, 1))
K10 = [SW(0), SW(2), CCX] * 4


def between(pre, word):
    return pre + word + pre[::-1]


K01 = between([SW(0)], K10)
K20 = between([SW(1)], K10)
K02 = between([SW(1)], K01)
K30 = between([SW(2)], K20)
K03 = between([SW(2)], K02)
# K_ab: its word, and the swaps around K, the innermost first.
KS = {'10': (K10, ()), '01': (K01, (0,)), '20': (K20, (1,)),
      '02': (K02, (0, 1)), '30': (K30, (1, 2)), '03': (K03, (0, 1, 2))}

#  i: (wires of the X gates around K_ab, ab)
CYCLE = {
    0: ((1, 2, 3), '01'), 1: ((2, 3), '10'), 2: ((0, 2, 3), '02'),
    3: ((0, 3), '20'), 4: ((3,), '01'), 5: ((1, 3), '10'),
    6: ((0, 1, 3), '03'), 7: ((0, 1), '30'), 8: ((1,), '01'),
    9: ((), '10'), 10: ((0,), '02'), 11: ((0, 2), '20'),
    12: ((2,), '01'), 13: ((1, 2), '10'),
}
OMEGA = {i: between([X(w) for w in xs], KS[k][0])
         for i, (xs, k) in CYCLE.items()}


# The same cycles as commutators of two Toffoli gates: the form that the
# definition unfolds to.  K is T C T C with T = CCX(3 0 -> 1) and
# C = CCX(2 1 -> 0); a swap around it renames two wires, and an X gate
# around it negates a control on its wire (and commutes with a target).

def rename(g, a, b):
    f = {a: b, b: a}
    _, t, cs = g
    return X(f.get(t, t), *((f.get(c, c), v) for c, v in cs))


def negate(g, w):
    _, t, cs = g
    return X(t, *((c, v ^ (c == w)) for c, v in cs))


def form(i):
    xs, k = CYCLE[i]
    pair = [X(1, (3, 1), (0, 1)), CCX]              # T, C
    for d in KS[k][1]:                              # innermost swap first
        pair = [rename(g, d, d + 1) for g in pair]
    for w in xs:
        pair = [negate(g, w) for g in pair]
    return pair * 2


# ---------------------------------------------------------------------
# Lafont's canonical forms on sixteen points.

def stairs(d, j):
    """The indices of the cycles of the stairs from d to j."""
    assert 0 <= d <= N - 3 and d <= j <= N - 1
    return list(range(d, j)) if j <= N - 2 else list(range(d, N - 2)) + [N - 3]


def word_perm(w):
    p = IDENT
    for i in w:
        p = mul(p, omega(i))
    return p


def targets(p):
    js, q = [], p
    for d in range(N - 2):
        js.append(q[d])
        q = mul(q, inv(word_perm(stairs(d, q[d]))))
    assert q == IDENT, 'not an even permutation'
    return js


def canonical(js):
    """The canonical form with the targets js: the highest stairs first."""
    return [i for d in reversed(range(N - 2)) for i in stairs(d, js[d])]


# ---------------------------------------------------------------------
# Drawing, with the dimensions and the primitives of rule-*.tex.

SPACING, WIRESTEP, MARGIN, GAP = .40, .36, .13, .14


def picture(groups, n=4, labels=False):
    """groups: a list of (label or None, columns); a column is a list of
    gates drawn at the same place."""
    def y(w):
        return -(n - 1 - w) * WIRESTEP
    body, x, spans = [], MARGIN, []
    for k, (label, columns) in enumerate(groups):
        if k:
            x += GAP
        first = x + SPACING / 2
        for column in columns:
            c = x + SPACING / 2
            for g in column:
                if g[0] == 'X':
                    _, t, cs = g
                    ws = [t] + [w for w, _ in cs]
                    if cs:
                        body.append(r'\draw (%.3f,%.3f)--(%.3f,%.3f);'
                                    % (c, y(max(ws)), c, y(min(ws))))
                    for w, v in cs:
                        body.append(r'\filldraw[fill=%s] (%.3f,%.3f) circle[radius=1.5pt];'
                                    % ('black' if v else 'white', c, y(w)))
                    body.append(r'\draw[fill=white] (%.3f,%.3f) circle[radius=3pt];' % (c, y(t)))
                    body.append(r'\draw (%.3f,%.3f)--(%.3f,%.3f) (%.3f,%.3f)--(%.3f,%.3f);'
                                % (c - .105, y(t), c + .105, y(t), c, y(t) - .105, c, y(t) + .105))
                else:
                    _, d = g
                    l, r, a, b = c - SPACING * .38, c + SPACING * .38, y(d + 1), y(d)
                    body += [
                        r'\draw[white,line width=2pt] (%.3f,%.3f)--(%.3f,%.3f) (%.3f,%.3f)--(%.3f,%.3f);'
                        % (l, a, r, a, l, b, r, b),
                        r'\draw (%.3f,%.3f)--(%.3f,%.3f);' % (l, a, r, b),
                        r'\draw[white,line width=2pt] (%.3f,%.3f)--(%.3f,%.3f);' % (l, b, r, a),
                        r'\draw (%.3f,%.3f)--(%.3f,%.3f);' % (l, b, r, a)]
            x += SPACING
        spans.append((label, first, x - SPACING / 2))
    end = x + MARGIN
    out = [r'\begin{tikzpicture}[x=1cm,y=1cm,baseline={([yshift=-0.25em]mid)},line width=.45pt]',
           r'\coordinate (mid) at (0,%.3f);' % (y(0) / 2)]
    for w in reversed(range(n)):
        out.append(r'\draw (0,%.3f)--(%.3f,%.3f);' % (y(w), end, y(w)))
        if labels:
            out.append(r'\node[anchor=east,font=\scriptsize,inner sep=0pt] at (-.08,%.3f) {$%d$};' % (y(w), w))
    out += body
    for label, a, b in spans:
        if label:
            yb = y(0) - .27
            out.append(r'\draw[line width=.3pt] (%.3f,%.3f)--(%.3f,%.3f)--(%.3f,%.3f)--(%.3f,%.3f);'
                       % (a - .15, yb + .06, a - .15, yb, b + .15, yb, b + .15, yb + .06))
            out.append(r'\node[anchor=north,font=\scriptsize,inner sep=2pt] at (%.3f,%.3f) {$%s$};'
                       % ((a + b) / 2, yb, label))
    out.append(r'\end{tikzpicture}')
    return '\n'.join(out)


def flat(groups):
    return [g for _, columns in groups for column in columns for g in column]


def write(name, groups, **kw):
    (OUT / (name + '.tex')).write_text(
        '% Generated by draw_canon.py.\n' + picture(groups, **kw) + '\n',
        encoding='utf-8')


def main():
    # The cycles and their forms.
    for i in range(14):
        assert perm(OMEGA[i]) == omega(i), i
        assert perm(form(i)) == omega(i), i
    sizes = [len(OMEGA[i]) for i in range(14)]
    assert (min(sizes), max(sizes)) == (12, 24)

    # The stairs, and the number of canonical forms.
    for d in range(N - 2):
        for j in range(d, N):
            p = word_perm(stairs(d, j))
            assert p[d] == j and all(p[x] == x for x in range(d))
    count = 1
    for d in range(N - 2):
        count *= N - d
    assert count == 20922789888000 // 2             # 16!/2

    # The example: the Toffoli gate exchanges the positions 4, 5 and 10, 11.
    toffoli = perm([CCX])
    assert [(i, x) for i, x in enumerate(toffoli) if i < x] == [(4, 5), (10, 11)]
    assert (GRAY[4], GRAY[5], GRAY[10], GRAY[11]) == (0b0110, 0b0111, 0b1111, 0b1110)
    js = targets(toffoli)
    assert js == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 10, 11, 12, 13]
    assert canonical(js) == [9, 8, 7, 6, 5, 4]
    # Dividing by the stairs moves the first exchange one position up.
    q = toffoli
    for d in range(4, 9):
        assert [(i, x) for i, x in enumerate(q) if i < x] == [(d, d + 1), (10, 11)]
        q = mul(q, inv(omega(d)))
    assert q == omega(9)
    letters = sum(len(OMEGA[i]) for i in canonical(js))
    assert letters == 104

    # The swap of the wires 1 and 2: S_10(12) S_8(12) S_4(6) S_2(6).
    js1 = targets(perm([SW(1)]))
    assert [(d, j) for d, j in enumerate(js1) if j != d] == [(2, 6), (4, 6), (8, 12), (10, 12)]
    assert canonical(js1) == [10, 11, 8, 9, 10, 11, 4, 5, 2, 3, 4, 5]

    # The figure.  (a) Omega_9 as written, and as a commutator.
    word = [(None, [[SW(0), SW(2)], [CCX]] * 4)]
    assert flat(word) == OMEGA[9]
    commutator = [(None, [[g] for g in form(9)])]
    assert form(9) == [X(1, (3, 1), (0, 1)), CCX] * 2
    assert perm(flat(commutator)) == omega(9)
    # (b) The Toffoli gate and its canonical circuit.
    gate = [(None, [[CCX]])]
    canon = [(r'\Omega_{%d}' % i, [[g] for g in form(i)]) for i in canonical(js)]
    assert perm(flat(canon)) == toffoli
    write('canon-cycle-word', word, labels=True)
    write('canon-cycle-form', commutator)
    write('canon-toffoli-gate', gate, labels=True)
    write('canon-toffoli-form', canon)
    print('PASS: 14 cycles and their commutator forms, the stairs, the Toffoli')
    print('      example (targets %s, %d letters), the swap of the wires 1 2' % (js, letters))
    print('Wrote canon-cycle-word, canon-cycle-form, canon-toffoli-gate, canon-toffoli-form')
    for i in canonical(js):
        print('  Omega_%d = (%s)^2' % (i, ' '.join(
            'CCX[%s->%d]' % (' '.join(('' if v else '~') + str(c) for c, v in cs), t)
            for _, t, cs in form(i)[:2])))


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Draw Lafont's cycles, relations and canonical forms of even permutations
as circuits on the points (fig:lafont of the case study, Section 4, and
fig:xcxccx-lafont of Section 7).

Lafont draws a permutation of N points as a circuit with one wire for each
point, and his generator omega as a gate on three adjacent wires: the wire
of the point i goes to i + 1, that of i + 1 to i + 2, and that of i + 2 to
i.  Here time runs left to right and the point 0 is the bottom wire, as in
the other circuits of the paper, so a picture is Lafont's turned a quarter
of a turn.  Writes, next to this file,

  lafont-cycle.tex    the cycle omega_i
  lafont-order-l.tex, lafont-order-r.tex, lafont-near-l.tex,
  lafont-near-r.tex, lafont-far-l.tex, lafont-far-r.tex
                      the two sides of each relation of Lafont's Theorem 4,
                      omega_i omega_i omega_i = 1, omega_i omega_{i+1}
                      omega_i = omega_{i+1} omega_{i+1} and omega_i
                      omega_{i+2} omega_i = omega_{i+2} omega_i omega_{i+1},
                      products in diagram order
  lafont-c2-j.tex, lafont-c3-j.tex
                      the stairs s_0(j) from the point 0 on three and four
                      points, the coset representatives
  lafont-rulek-l.tex, lafont-rulek-r.tex
                      the two sides of the k-th of the seven rewriting
                      rules of Lafont's Fig. 10
  lafont-six.tex      the canonical form s_3(4) s_2(3) s_1(5) s_0(3) of an
                      even permutation of six points, its stairs bracketed
  lafont-toffoli.tex  the canonical form omega_9 ... omega_4 of the
                      permutation of the Toffoli gate of the example, on
                      the sixteen positions

Nothing is written until every picture has passed its checks: the height
at which each strand ends is the image of its point under the product of
the cycles, the two sides of each relation have the same permutation,
the targets of that permutation are the ones the picture
claims, and the last one is the permutation that draw_canon.py computes
for the Toffoli gate.  Python 3, no dependencies:  python draw_lafont.py
"""
from pathlib import Path

import draw_canon as C

OUT = Path(__file__).resolve().parent


# ---------------------------------------------------------------------
# Permutations of n points, as tuples; mul(p, q) applies p and then q.

def omega(i, n):
    p = list(range(n))
    p[i], p[i + 1], p[i + 2] = i + 1, i + 2, i
    return tuple(p)


def mul(p, q):
    return tuple(q[x] for x in p)


def inv(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def word_perm(word, n):
    p = tuple(range(n))
    for i in word:
        p = mul(p, omega(i, n))
    return p


def stairs(d, j, n):
    """The indices of the cycles of the stairs from d to j among n points."""
    assert 0 <= d <= n - 3 and d <= j <= n - 1
    return list(range(d, j)) if j <= n - 2 else list(range(d, n - 2)) + [n - 3]


def targets(p):
    n, js, q = len(p), [], p
    for d in range(n - 2):
        js.append(q[d])
        q = mul(q, inv(word_perm(stairs(d, q[d], n), n)))
    assert q == tuple(range(n)), 'not an even permutation'
    return js


# ---------------------------------------------------------------------
# Drawing.  A group is (label or None, [indices of cycles]); the cycles of
# a group are drawn side by side, and the groups a little apart.

def picture(groups, n, step, width, names=None, font=r'\scriptsize',
            gap=.16, margin=.22, labels=True):
    def y(level):
        return -(n - 1 - level) * step
    level = list(range(n))                  # the height of each strand
    paths = [[(0.0, y(p))] for p in range(n)]
    x, spans, gates = margin, [], []
    for k, (label, word) in enumerate(groups):
        if k:
            x += gap
        first = x
        for i in word:
            # The gate: a grey box over the three wires that it permutes.
            gates.append(r'\fill[black!11,rounded corners=1.5pt] (%.3f,%.3f) rectangle (%.3f,%.3f);'
                         % (x + .03, y(i) - .42 * step, x + width - .03, y(i + 2) + .42 * step))
            for p in range(n):
                here = level[p]
                if here in (i, i + 1, i + 2):
                    there = {i: i + 1, i + 1: i + 2, i + 2: i}[here]
                    paths[p] += [(x + .03, y(here)), (x + width - .03, y(there))]
                    level[p] = there
            x += width
        spans.append((label, first, x))
    end = x + margin
    for p in range(n):
        paths[p].append((end, y(level[p])))
    out = [r'\begin{tikzpicture}[x=1cm,y=1cm,baseline={([yshift=-0.25em]mid)},line width=.45pt]',
           r'\coordinate (mid) at (0,%.3f);' % (y(0) / 2)]
    out += gates
    for p in range(n):
        pts = []
        for q in paths[p]:                  # drop repeated points
            if not pts or abs(q[0] - pts[-1][0]) + abs(q[1] - pts[-1][1]) > 1e-9:
                pts.append(q)
        out.append(r'\draw[rounded corners=1pt] '
                   + '--'.join('(%.3f,%.3f)' % q for q in pts) + ';')
        # Each strand carries the name of its point at both ends.
        if not labels:
            continue
        name = names[p] if names else str(p)
        out.append(r'\node[anchor=east,font=%s,inner sep=0pt] at (-.08,%.3f) {$%s$};'
                   % (font, y(p), name))
        out.append(r'\node[anchor=west,font=%s,inner sep=0pt] at (%.3f,%.3f) {$%s$};'
                   % (font, end + .08, y(level[p]), name))
    for label, a, b in spans:
        if label:
            yb = y(0) - .42 * step - .11
            out.append(r'\draw[line width=.3pt] (%.3f,%.3f)--(%.3f,%.3f)--(%.3f,%.3f)--(%.3f,%.3f);'
                       % (a + .04, yb + .06, a + .04, yb, b - .04, yb, b - .04, yb + .06))
            out.append(r'\node[anchor=north,font=\scriptsize,inner sep=2pt] at (%.3f,%.3f) {$%s$};'
                       % ((a + b) / 2, yb, label))
    out.append(r'\end{tikzpicture}')
    return '\n'.join(out), tuple(level)


PICTURES = []                               # (name, text), written at the end


def draw(name, groups, n, **kw):
    """Draw a picture, keep it for writing, and return where its strands end."""
    body, ends = picture(groups, n, **kw)
    word = [i for _, w in groups for i in w]
    assert ends == word_perm(word, n), name  # the strands are the permutation
    PICTURES.append((name, '% Generated by draw_lafont.py.\n' + body + '\n'))
    return ends


def main():
    # (a) The cycle: i -> i + 1 -> i + 2 -> i.
    ends = draw('lafont-cycle', [(None, [0])], 3, step=.36, width=.5,
                names=['i', 'i{+}1', 'i{+}2'])
    assert ends == (1, 2, 0)

    # The relations of Lafont's Theorem 4, on the points i, ..., i + 4
    # (index 0 here), each side a word of cycles in diagram order.
    for name, left, right, n in (('order', [0, 0, 0], [], 3),
                                 ('near', [0, 1, 0], [1, 1], 4),
                                 ('far', [0, 2, 0], [2, 0, 1], 5)):
        ends_l = draw('lafont-%s-l' % name, [(None, left)], n,
                      step=.2, width=.32, labels=False)
        ends_r = draw('lafont-%s-r' % name, [(None, right)], n,
                      step=.2, width=.32, labels=False)
        assert ends_l == ends_r, name

    # The coset representatives on three and four points: the stairs
    # s_0(j), which carry the point 0 to j, the last repeating its cycle.
    for n in (3, 4):
        for j in range(n):
            ends = draw('lafont-c%d-%d' % (n - 1, j), [(None, stairs(0, j, n))], n,
                        step=.2, width=.34, labels=False)
            assert ends[0] == j

    # The seven rules of Lafont's Fig. 10, the clauses of the coset table,
    # in the reading order of the figure; each side a word in diagram order.
    rules = [([0, 2], [2, 2, 1, 2, 0], 5),
             ([0, 1, 2, 0], [2, 0, 1, 2], 5),
             ([0, 1, 0], [1, 1], 4),
             ([0, 0], [1, 0, 1], 4),
             ([0, 1, 2, 2, 0], [1, 0, 1, 2, 2], 5),
             ([0, 1, 1, 0], [1, 1, 0, 1, 1], 4),
             ([0, 0, 0], [], 3)]
    for k, (left, right, n) in enumerate(rules, 1):
        ends_l = draw('lafont-rule%d-l' % k, [(None, left)], n,
                      step=.16, width=.3, margin=.14, labels=False)
        ends_r = draw('lafont-rule%d-r' % k, [(None, right)], n,
                      step=.16, width=.3, margin=.14, labels=False)
        assert ends_l == ends_r, k

    # (b) A canonical form on six points, one stairs for each d, the
    # highest first: a stairs of one cycle (twice), the stairs to the last
    # point, which repeats its last cycle, and a stairs of three cycles.
    n, js = 6, [3, 5, 3, 4]
    six = [('s_{%d}(%d)' % (d, js[d]), stairs(d, js[d], n))
           for d in reversed(range(n - 2))]
    assert [w for _, w in six] == [[3], [2], [1, 2, 3, 3], [0, 1, 2]]
    ends = draw('lafont-six', six, n, step=.36, width=.5, gap=.3)
    assert targets(ends) == js
    # The caption: the stairs s_d(j) raises the strand of the point d to
    # the height j, one wire at each cycle.
    level = list(range(n))
    for d in reversed(range(n - 2)):
        assert level[d] == d                # not yet moved by a higher stairs
        for k, i in enumerate(stairs(d, js[d], n)):
            level = [{i: i + 1, i + 1: i + 2, i + 2: i}.get(h, h) for h in level]
            assert level[d] == d + k + 1
        assert level[d] == js[d]
    for d in range(n - 2):                  # what a stairs does to the points
        for j in range(d, n):
            p = word_perm(stairs(d, j, n), n)
            assert p[d] == j and all(p[x] == x for x in range(d))

    # (c) The example: the canonical form of the permutation of the Toffoli
    # gate, which exchanges the positions 4, 5 and 10, 11.
    toffoli = C.perm([C.CCX])
    word = C.canonical(C.targets(toffoli))
    assert word == [9, 8, 7, 6, 5, 4]
    ends = draw('lafont-toffoli', [(r'\omega_{%d}' % i, [i]) for i in word],
                16, step=.2, width=.46, font=r'\tiny', gap=0)
    assert ends == toffoli
    assert [(i, x) for i, x in enumerate(ends) if i < x] == [(4, 5), (10, 11)]

    for name, text in PICTURES:
        (OUT / (name + '.tex')).write_text(text, encoding='utf-8')
    print('PASS: the cycle, the three relations and the seven rules (both sides')
    print('      alike), the stairs from 0 on three and four points,')
    print('      the canonical form of six points (targets %s),' % js)
    print('      and the canonical form of the Toffoli gate on sixteen points')
    print('Wrote', ', '.join(name for name, _ in PICTURES))


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Draw Lafont's canonical forms of even permutations as circuits on the
points (fig:xcxccx-lafont of Section 6).

Lafont draws a permutation of N points as a circuit with one wire for each
point, and his generator omega as a gate on three adjacent wires: the wire
of the point i goes to i + 1, that of i + 1 to i + 2, and that of i + 2 to
i.  Here time runs left to right and the point 0 is the bottom wire, as in
the other circuits of the paper, so a picture is Lafont's turned a quarter
of a turn.  Writes, next to this file,

  lafont-cycle.tex    the cycle omega_i
  lafont-six.tex      the canonical form s_3(4) s_2(3) s_1(5) s_0(3) of an
                      even permutation of six points, its stairs bracketed
  lafont-toffoli.tex  the canonical form omega_9 ... omega_4 of the
                      permutation of the Toffoli gate of the example, on
                      the sixteen positions

Every picture is checked before it is written: the height at which each
strand ends is the image of its point under the product of the cycles, the
targets of that permutation are the ones the picture claims, and the last
one is the permutation that draw_canon.py computes for the Toffoli gate.
Python 3, no dependencies:  python draw_lafont.py
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
            gap=.16, margin=.22):
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


def write(name, groups, n, **kw):
    body, ends = picture(groups, n, **kw)
    word = [i for _, w in groups for i in w]
    assert ends == word_perm(word, n), name  # the strands are the permutation
    (OUT / (name + '.tex')).write_text(
        '% Generated by draw_lafont.py.\n' + body + '\n', encoding='utf-8')
    return ends


def main():
    # (a) The cycle: i -> i + 1 -> i + 2 -> i.
    ends = write('lafont-cycle', [(None, [0])], 3, step=.36, width=.5,
                 names=['i', 'i{+}1', 'i{+}2'])
    assert ends == (1, 2, 0)

    # (b) A canonical form on six points, one stairs for each d, the
    # highest first: a stairs of one cycle (twice), the stairs to the last
    # point, which repeats its last cycle, and a stairs of three cycles.
    n, js = 6, [3, 5, 3, 4]
    six = [('s_{%d}(%d)' % (d, js[d]), stairs(d, js[d], n))
           for d in reversed(range(n - 2))]
    assert [w for _, w in six] == [[3], [2], [1, 2, 3, 3], [0, 1, 2]]
    ends = write('lafont-six', six, n, step=.36, width=.5, gap=.3)
    assert targets(ends) == js
    # The caption: the stairs from d to j raises the strand of the point d
    # to the height j, one wire at each cycle.
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
    ends = write('lafont-toffoli', [(r'\omega_{%d}' % i, [i]) for i in word],
                 16, step=.2, width=.46, font=r'\tiny', gap=0)
    assert ends == toffoli
    assert [(i, x) for i, x in enumerate(ends) if i < x] == [(4, 5), (10, 11)]
    print('PASS: the cycle, the canonical form of six points (targets %s),' % js)
    print('      and the canonical form of the Toffoli gate on sixteen points')
    print('Wrote lafont-cycle, lafont-six, lafont-toffoli')


if __name__ == '__main__':
    main()

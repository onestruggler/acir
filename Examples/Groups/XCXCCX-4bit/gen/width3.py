"""Proposition B.3: completeness on three wires, by the Coxeter presentation of S8.

Wires: our wire 2 is the paper's x1, wire 1 its x2, wire 0 its x3.  The
states, in the Gray order 000, 001, 011, 010, 110, 111, 101, 100 (x1 x2 x3),
are numbered 0..7, and T d is the edge Toffoli swapping states d, d+1.

An edge Toffoli is spelled canonically by its direction (target wire) and
the values of its two controls:
  direction 0:  [X2] [X1] CCX0 [X1] [X2]                 (controls w2, w1)
  direction 1:  [X2] [X0] SW0 CCX0 SW0 [X0] [X2]         (controls w2, w0)
  direction 2:  [X1] [X0] SW1 SW0 CCX0 SW0 SW1 [X0] [X1] (controls w1, w0)
with X on a control whose value is 0.  The lemmas follow Appendix B:
Lemma B.4 in direction 0 (phase A), carried to the other directions by
swaps (B), the conjugation of every edge Toffoli by every symmetry letter
(C), Lemma B.5's two base relations from (6) and (3) (D), every other
Coxeter relation by a symmetry of the cube (E), and the gates as words in
the T d (F).
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from derive import Lib, parse, show, BASE, canon  # noqa: E402
from search import Searcher, Table  # noqa: E402
from xc import perm  # noqa: E402
from cube3 import sym_words, transport, inv_perm, GRAY  # noqa: E402

APPA3 = [
    ('Wc⁼', 'X2 CCX0 X2 CCX0', 'CX0'),
    ('cq⁼', 'CCX0 CX0', 'CX0 CCX0'),
    ('em⁼', 'SW0 CCX0 SW0 X2 SW0 CCX0 SW0 X2', 'SW0 CX0 SW0'),
    ('me⁼', 'X2 SW0 CCX0 SW0 X2 SW0 CCX0 SW0', 'SW0 CX0 SW0'),
    ('CCX²⁼', 'CCX0 CCX0', ''),
]


def spell(direction, a, b):
    """Canonical edge Toffoli: direction t, control values (a, b) on the two other wires
    (wires listed high to low)."""
    if direction == 0:
        core, cw = 'CCX0', (2, 1)
    elif direction == 1:
        core, cw = 'SW0 CCX0 SW0', (2, 0)
    else:
        core, cw = 'SW1 SW0 CCX0 SW0 SW1', (1, 0)
    xs = [('X%d' % w) for w, v in zip(cw, (a, b)) if v == 0]
    return ' '.join(xs + [core] + list(reversed(xs)))


def edge_of(a, b):
    """(direction, control values) of the edge {a, b}."""
    d = (a ^ b).bit_length() - 1
    others = [w for w in (2, 1, 0) if w != d]
    return d, tuple((a >> w) & 1 for w in others)


def spell_edge(e):
    a, b = sorted(e)
    d, vals = edge_of(a, b)
    return spell(d, *vals)


T = {}
for _d in range(7):
    T[_d] = spell_edge((GRAY[_d], GRAY[_d + 1]))


class Gen3:
    def __init__(self):
        lib = Lib(3)
        for nm, a, l, r in BASE:
            if nm in ('r1⁼', 'σσ⁼', 'r4⁼', 'r5⁼', 'r6⁼', 'σCX⁼', 'σσσ⁼'):
                lib.add(nm, a, parse(l), parse(r))
        for nm, l, r in APPA3:
            lib.add(nm, 3, parse(l), parse(r))
        self.S = Searcher(lib, [(2, Table(2), 'by2')])
        self.out = []
        self.names = set()

    def lemma(self, name, wps, doc='', depth=4):
        t = time.time()
        txt = self.S.derivation(name, 3, wps, depth=depth)
        self.S.lib.add(name, 3, parse(wps[0]), parse(wps[-1]))
        self.out.append(('-- ' + doc + '\n' if doc else '') + txt)
        self.names.add(name)
        dt = time.time() - t
        if dt > 5:
            print('  slow', name, round(dt, 1), flush=True)
        return name


def W(*parts):
    return ' '.join(p for p in parts if p)


def build():
    G = Gen3()
    L = G.lemma
    T0, T1, T2, T3, T4, T5, T6 = (T[i] for i in range(7))
    CXa, CXb = 'CX0', 'SW1 CX0 SW1'

    # ---------------------------------------------------------------- A
    for i in range(7):
        if i == 3:
            L('T3²⁼', [W(T3, T3), 'X0 SW1 SW0 CCX0 SW0 SW1 SW1 SW0 CCX0 SW0 SW1 X0',
                       'X0 SW1 SW0 CCX0 SW0 SW0 CCX0 SW0 SW1 X0', 'X0 SW1 SW0 CCX0 CCX0 SW0 SW1 X0',
                       'X0 SW1 SW0 SW0 SW1 X0', 'X0 SW1 SW1 X0', 'X0 X0', ''], 'T 3 is an involution')
            continue
        L('T%d²⁼' % i, [W(T[i], T[i]), ''], 'T %d is an involution' % i, depth=6)
    L('T4T6⁼', [W(T4, T6), CXb], 'T4 T6 is the CNOT from wire 2 to wire 0')
    L('T6T4⁼', [W(T6, T4), CXb], 'T6 T4 is the CNOT from wire 2 to wire 0')
    L('X0a⁼', ['X0', W(CXb, 'X2', CXb, 'X2'), W(T4, T6, 'X2', CXb, 'X2'),
               W(T4, T6, 'X2', T4, T6, 'X2'), W(T4, T6, T2, T0)], 'X on wire 0 is T4 T6 T2 T0')
    L('X0b⁼', ['X0', W(CXa, 'X1', CXa, 'X1'), W(T4, T2, 'X1', CXa, 'X1'),
               W(T4, T2, 'X1', T4, T2, 'X1'), W(T4, T2, T6, T0)], 'X on wire 0 is T4 T2 T6 T0')
    L('far26⁼', [W(T2, T6), W(T4, T4, T2, T6, T0, T0), W(T4, 'X0', T0),
                 W(T4, T4, T6, T2, T0, T0), W(T6, T2)], 'T2 T6 = T6 T2')
    L('far24⁼', [W(T2, T4), CXa, W(T4, T2)], 'T2 T4 = T4 T2')
    L('far46⁼', [W(T4, T6), CXb, W(T6, T4)], 'T4 T6 = T6 T4')
    L('far04⁼', [W(T0, T4), W('X1', T2, 'X1', 'X1', T6, 'X1'), W('X1', T2, T6, 'X1'),
                 W('X1', T6, T2, 'X1'), W('X1', T6, 'X1', 'X1', T2, 'X1'), W(T4, T0)], 'T0 T4 = T4 T0')
    L('far02⁼', [W(T0, T2), W('X2', T6, 'X2', 'X2', T4, 'X2'), W('X2', T6, T4, 'X2'),
                 W('X2', T4, T6, 'X2'), W('X2', T4, 'X2', 'X2', T6, 'X2'), W(T2, T0)], 'T0 T2 = T2 T0')
    L('far06⁼', [W(T0, T6), W('X1', T2, 'X1', 'X1', T4, 'X1'), W('X1', T2, T4, 'X1'),
                 W('X1', T4, T2, 'X1'), W('X1', T4, 'X1', 'X1', T2, 'X1'), W(T6, T0)], 'T0 T6 = T6 T0')
    L('X0T4⁼', [W('X0', T4), W(T4, T2, T6, T0, T4), W(T4, T2, T6, T4, T0), W(T4, T2, T4, T6, T0),
                W(T4, T4, T2, T6, T0), W(T4, 'X0')], 'X on wire 0 passes T4: Lemma B.4')
    # ---------------------------------------------------------------- B
    L('X1T5⁼', [W('X1', T5), W('SW0', 'X0', T4, 'SW0'), W('SW0', T4, 'X0', 'SW0'), W(T5, 'X1')],
      'X on wire 1 passes T5')
    base2 = spell(2, 1, 1)
    L('X2B⁼', [W('X2', base2), W('SW1 SW0', 'X0', T4, 'SW0 SW1'), W('SW1 SW0', T4, 'X0', 'SW0 SW1'),
               W(base2, 'X2')], 'X on wire 2 passes the edge Toffoli of direction 2')

    # ---------------------------------------------------------------- C
    # g E g = E′ for every symmetry letter g and every edge E.
    edges = []
    for a in range(8):
        for d in range(3):
            b = a ^ (1 << d)
            if a < b:
                edges.append((a, b))
    letter_perm = {g: perm(parse(g), 3) for g in ('X0', 'X1', 'X2', 'SW0', 'SW1')}
    resp = {}
    for (a, b) in edges:
        E = spell_edge((a, b))
        for g, p in letter_perm.items():
            img = (p[a], p[b])
            E2 = spell_edge(img)
            nm = 'cj%s-%d%d⁼' % (g, a, b)
            L(nm, [W(g, E, g), E2], depth=5)
            resp[(g, frozenset((a, b)))] = (nm, frozenset(img))

    def conj_chain(s, e):
        """Waypoints from s E s⁻¹ down to the canonical spelling of the image edge."""
        wps = []
        cur = frozenset(e)
        k = len(s)
        stages = [cur]
        for g in reversed(s):
            cur = resp[(g, cur)][1]
            stages.append(cur)
        # stage j: s[0..k-j-1] E_j s[k-j-1..0]
        for j in range(k + 1):
            pre = s[:k - j]
            wps.append(W(' '.join(pre), spell_edge(stages[j]), ' '.join(reversed(pre))))
        return wps

    # ---------------------------------------------------------------- D
    m, e, f, p = T1, T4, T5, 'SW0 CX0 SW0'
    L('far14⁼', [W(m, e), W(m, f, f, e, f, f), W(m, f, p, e, p, f), W(p, p, e, p, f), W(e, p, f),
                 W(e, m, f, f), W(e, m)], 'Lemma B.5: T1 T4 = T4 T1, from (6)')
    L('braid4⁼', ['CCX0 SW0 CCX0 SW0 CCX0', 'SW0 SW0 CCX0 SW0 CCX0 SW0 CCX0 SW0 SW0',
                  'SW0 SW0 CX0 SW0 CCX0 SW0 CX0 SW0 SW0', 'CX0 SW0 CCX0 SW0 CX0',
                  'SW0 CX0 SW0 CX0 CCX0 CX0 SW0 CX0 SW0', 'SW0 CX0 SW0 CCX0 SW0 CX0 SW0',
                  'SW0 CCX0 SW0 CCX0 SW0 CCX0 SW0'], 'Lemma B.5: T4 T5 T4 = T5 T4 T5, from (6) and (3)')

    # ---------------------------------------------------------------- E
    words = sym_words()
    ed = {d: frozenset((GRAY[d], GRAY[d + 1])) for d in range(7)}

    def transported(name, base_name, base_pair, base_lhs_order, target_pair, doc):
        """A relation between T's on target_pair from one on base_pair, by a cube symmetry."""
        s = transport([ed[base_pair[0]], ed[base_pair[1]]], [ed[target_pair[0]], ed[target_pair[1]]],
                      words)[0]
        si = tuple(reversed(s))
        S, Si = ' '.join(s), ' '.join(si)
        # lhs/rhs of the base relation as sequences of indices into base_pair
        bl, br = base_lhs_order
        tl = [target_pair[base_pair.index(x)] for x in bl]
        tr = [target_pair[base_pair.index(x)] for x in br]
        wps = [W(*[T[x] for x in tl])]
        # respell each factor as s T s⁻¹, left to right
        done = []
        for idx, x in enumerate(bl):
            chain = conj_chain(s, ed[x])
            assert spell_edge(ed[tl[idx]]) == chain[-1] or True
            for c in reversed(chain[:-1]):
                wps.append(W(*done, c, *[T[y] for y in tl[idx + 1:]]))
            done.append(chain[0])
        wps.append(W(S, *[T[x] for x in bl], Si))
        wps.append(W(S, *[T[x] for x in br], Si))
        done = []
        rest = [W(S, T[x], Si) for x in br]
        wps.append(W(*rest))
        for idx, x in enumerate(br):
            chain = conj_chain(s, ed[x])
            for c in chain[1:]:
                wps.append(W(*[T[y] for y in tr[:idx]], c, *rest[idx + 1:]))
        dedup = [wps[0]]
        for w in wps[1:]:
            if w != dedup[-1]:
                dedup.append(w)
        L(name, dedup, doc)

    for (i, j) in [(0, 3), (0, 5), (1, 3), (1, 6), (2, 5), (3, 5), (3, 6)]:
        transported('far%d%d⁼' % (i, j), 'far14⁼', (1, 4), ((1, 4), (4, 1)), (i, j),
                    'T%d T%d = T%d T%d, by a symmetry of the cube' % (i, j, j, i))
    transported('far15⁼', 'far24⁼', (2, 4), ((2, 4), (4, 2)), (1, 5), 'T1 T5 = T5 T1')
    for i in (0, 1, 2, 3, 5):
        transported('braid%d⁼' % i, 'braid4⁼', (4, 5), ((4, 5, 4), (5, 4, 5)), (i, i + 1),
                    'T%d T%d T%d = T%d T%d T%d, by a symmetry of the cube' % (i, i + 1, i, i + 1, i, i + 1))

    # ---------------------------------------------------------------- F
    L('genSW0⁼', ['SW0', 'CX0 SW0 CX0 SW0 CX0', W(T2, T4, 'SW0 CX0 SW0 CX0'),
                  W(T2, T4, T1, T5, 'CX0'), W(T2, T4, T1, T5, T2, T4)], 'the swap of wires 0, 1')
    L('genCX1⁼', ['CX1', W('SW0', 'SW1 CX0 SW1', 'SW0'), W('SW0', T4, T6, 'SW0')],
      'the CNOT from wire 2 to wire 1')
    L('genCXd1⁼', ['SW1 CX1 SW1', 'SW1 SW0 SW1 CX0 SW1 SW0 SW1', 'SW1 SW0 X1 CCX0 X1 CCX0 SW0 SW1',
                   'X0 SW1 SW0 CCX0 SW0 SW1 X0 SW1 SW0 CCX0 SW0 SW1', W(T3, 'X0', T3, 'X0')],
      'the CNOT from wire 1 to wire 2')
    L('genX1⁼', ['X1', 'SW0 X0 SW0'], 'X on wire 1')
    L('genX2⁼', ['X2', 'SW1 X1 SW1'], 'X on wire 2')
    return G


if __name__ == '__main__':
    t = time.time()
    G = build()
    print('lemmas', len(G.out), 'time', round(time.time() - t, 1))
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                             'width3_lemmas.json')
    with open(out, 'w', encoding='utf-8') as fh:
        json.dump(G.out, fh, ensure_ascii=False, indent=0)

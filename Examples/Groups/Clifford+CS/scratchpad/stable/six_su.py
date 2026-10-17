"""The borrowed-wire switch of the S-box on six wires (b6-box, b6-Su).

Canonical placement: Σ(1; 5, 2 | 3, 4), the S-box b-Sb2-0-41-3 one wire
up, wire 0 idle.  `dance`: its box, in the form t Q t Q (t = TOFF(3; 1,
5), Q = CCZ(3, 2, 4)), passes SWAP(0, 3) = CX(0→3) CX(3→0) CX(0→3), each
CX by windows: it conjugates t and Q to themselves times copies on wire
0, which pass the rest (by 2-wire pieces where they are disjoint from
it) and cancel; then the swap renames the box letter by letter.  `su`:
the S-box's box wire moves from 3 to 0 (its other letters avoid both).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen6 import *

cyc = [0, 1, 2, 3, 4]

t = at(Toff, [3, 1, 5]); Q = at(CCZ, [3, 2, 4])
t0 = at(Toff, [0, 1, 5]); Q0 = at(CCZ, [0, 2, 4])
X1 = at(CX10, [0, 3])          # CX(3 -> 0)
X2 = at(CX10, [3, 0])          # CX(0 -> 3)
SW = [X2, X1, X2]
M = at(Toff, [4, 2, 5]); s = at(CSl, [1, 4]); s3 = at(CS3, [1, 4])


def pieces(a, b, c):
    """CCZ(a, b, c) in Syntactics' spelling: CS_bc CX_ab CS_bc^3 CX_ab CS_ac."""
    return [at(CSl, [b, c]), at(CX01, [a, b]), at(CS3, [b, c]), at(CX01, [a, b]), at(CSl, [a, c])]


def pass_disjoint_left(d, i, qargs):
    """the CCZ at i (qargs) moves right past the gate at i + 1 (disjoint
    from it), through its pieces."""
    g = d.cur[i + 1]
    ps = pieces(*qargs)
    d.win(i, 1, ps)
    for j in reversed(range(len(ps))):
        d.win(i + j, 2, [g, ps[j]])
    d.win(i + 1, len(ps), [at(CCZ, list(qargs))])


def pass_X2(d, i):
    """X2 at i passes t Q t Q at i+1 .. i+4."""
    d.win(i, 2, [t, X2])
    d.win(i + 1, 2, [Q, Q0, X2])
    d.win(i + 3, 2, [t, X2])
    d.win(i + 4, 2, [Q, Q0, X2])
    # t Q Q0 t Q Q0 X2 from i
    pass_disjoint_left(d, i + 2, (0, 2, 4))       # Q0 past t
    d.win(i + 3, 2, [Q, Q0])                      # Q0 Q -> Q Q0
    d.win(i + 4, 2, [])                           # Q0 Q0 -> eps


def pass_X1(d, i):
    """X1 at i passes t Q t Q at i+1 .. i+4."""
    d.win(i, 2, [t, t0, X1])
    d.win(i + 2, 2, [Q, X1])
    d.win(i + 3, 2, [t, t0, X1])
    d.win(i + 5, 2, [Q, X1])
    # t t0 Q t t0 Q X1 from i: t0 at i+1 past Q at i+2
    g = d.cur[i + 1]
    ps = pieces(3, 2, 4)
    d.win(i + 2, 1, ps)
    for j in range(len(ps)):
        d.win(i + 1 + j, 2, [ps[j], g])
    d.win(i + 1, len(ps), [Q])
    # t Q t0 t t0 Q
    d.win(i + 2, 2, [t, t0])
    d.win(i + 3, 2, [])


def build():
    a = Deriv('pass₂', [X2, t, Q, t, Q])
    pass_X2(a, 0)
    b = Deriv('pass₁', [X1, t, Q, t, Q])
    pass_X1(b, 0)
    d = Deriv('dance', [t, Q, t, Q])
    d.win(0, 0, SW + SW)
    d.lemma(5, a, list(range(6)))
    d.lemma(4, b, list(range(6)))
    d.lemma(3, a, list(range(6)))
    for j in range(4):
        new = t0 if d.cur[j + 3].lit is Toff else Q0
        d.win(j, 4, [new] + SW)
    d.win(4, 6, [])
    assert [g.f for g in d.cur] == [g.f for g in [t0, Q0, t0, Q0]]
    dance = d
    global PASS
    PASS = (a, b)

    u = Deriv('su', [PG(Sig0, cyc)])
    u.split(0, Sig0, Bx0, R0)
    u.win(0, 1, [t, Q, t, Q], idle=0)
    u.win(4, 1, [M, s, M, s3], idle=0)
    u.lemma(0, dance, list(range(6)))
    rho_u = bubble([1, 2, 0, 4, 5], N)
    u.win(0, 4, [PG(Bx0, rho_u)], idle=3)
    u.win(1, 4, [PG(R0, rho_u)], idle=3)
    u.merge(0, Sig0)
    return dance, u


if __name__ == '__main__':
    dance, u = build()
    a, b = PASS
    print(len(a.steps), len(b.steps), len(dance.steps), 'dance steps;', len(u.steps), 'su steps')
    module('Pass2', 'CX(0→3) passes the box with box wire 3 on six wires',
           """The box with box wire 3 and controls 1, 5, 2, 4, written t Q t Q
(t = TOFF(3; 1, 5), Q = CCZ(3, 2, 4)), and CX(0→3), wire 0 idle in the
box: the CX passes t and turns Q into Q CCZ(0, 2, 4), whose second
factor passes t through the two-wire pieces of the CCZ and cancels.""",
           [a], script='six_su.py')
    module('Pass1', 'CX(3→0) passes the box with box wire 3 on six wires',
           """As Stable.Six.Pass2 with CX(3→0): the CX passes Q and turns t into
t TOFF(0; 1, 5), whose second factor passes Q through the two-wire pieces
of the CCZ and cancels.""",
           [b], script='six_su.py')
    module('Dance', 'The box of the S-box passes the swap of its box wire and an idle wire',
           """On six wires, Σ(1; 5, 2 | 3, 4)'s box with box wire 3 and controls 1,
5, 2, 4, written t Q t Q (t = TOFF(3; 1, 5), Q = CCZ(3, 2, 4)), equals the
box with box wire 0, t′ Q′ t′ Q′: the swap of the wires 0 3, as
CX(0→3) CX(3→0) CX(0→3), passes t Q t Q CX by CX — each conjugates t and
Q to themselves times copies on wire 0, which pass the rest, through the
two-wire pieces of a CCZ where they are disjoint from it, and cancel —
and then renames the box letter by letter (the joint paper's b6-box).""",
           [dance], imports=['open import Examples.Groups.Clifford+CS.Stable.Six.Pass1 c₅ using (pass₁)',
                             'open import Examples.Groups.Clifford+CS.Stable.Six.Pass2 c₅ using (pass₂)'],
           script='six_su.py')
    module('Su', "The S-box's box wire moves to an idle wire",
           """Σ(1; 5, 2 | 3, 4) = Σ(1; 5, 2 | 0, 4) on six wires: the S-box
b-Sb2-0-41-3 one wire up is its box followed by letters that avoid the
wires 0 and 3; the box moves by Stable.Six.Dance (the joint paper's
b6-Su).""",
           [u], imports=['open import Examples.Groups.Clifford+CS.Stable.Six.Dance c₅ using (dance)'],
           script='six_su.py')

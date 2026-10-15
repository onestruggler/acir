# The lemma dictionary of the five-wire derivations: name -> (lhs, rhs).
# It starts with the five-wire rules, assumed (lower5.py treats every
# entry that no derivation proves as an axiom at its canonical placement):
#
#   AX   the CS of the borrowed wires 0, 1 of the S-box with x = 2,
#        t = 3, y = 4 commutes with its commutator part
#        [Toff(1; 3, 4), CS(2, 1)] (Five/Rules.AX).
from derivn import norm

T134 = ('TOFF', 1, 3, 4)
L = {
    'AX': (norm([('CS', 0, 1), T134, ('CS', 1, 2), T134, ('CSd', 1, 2)]),
           norm([T134, ('CS', 1, 2), T134, ('CSd', 1, 2), ('CS', 0, 1)])),
}

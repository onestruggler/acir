# First lemmas of the four-wire calculus with the schema, checked step
# by step (deriv.py).  Every step is a three-wire window, a structural
# commutation, the schema, or an earlier lemma.
from deriv import Derivation, show, fp

L = {}

# Lemma 0: two CCZs sharing two wires commute.  With a = CCZ_312,
# b = CCZ_012 and c = CX_30 the schema reads c b c = b a, so
#   a b -> a b (c b c)(c b c) -> a b (b a)(c b c) -> a (b b) a c b c
#      -> a a c b c -> c b c -> b a.
a, b, c = ('CCZ', 3, 1, 2), ('CCZ', 0, 1, 2), ('CX', 3, 0)
d = Derivation('CCZ312-CCZ012', [a, b], [b, a], L)
d.win(2, 2, [c, c])                # a b c c          (c c = eps on {0,3})
d.win(3, 3, [b, b])                # a b c b b c      (b b = eps on {0,1,2})
d.win(4, 4, [c, c])                # a b c b c c b c  (c c = eps on {0,3})
d.delta(2)                         # a b (b a) c b c
d.win(1, 3, [])                    # a a c b c        (b b = eps)
d.win(0, 2, [])                    # c b c            (a a = eps on {1,2,3})
d.delta(0)                         # b a
L = d.done()

# Lemma 0b: CCZ_123 commutes with CX_30 (Barenco pieces of the CCZ with
# target 3 each pass the CNOT in a window of three wires).
E, N = ('CCZ', 1, 2, 3), ('CX', 3, 0)
d = Derivation('CCZ123-CX30', [E, N], [N, E], L)
d.win(0, 1, [('CS', 2, 3), ('CX', 1, 2), ('CSd', 2, 3), ('CX', 1, 2), ('CS', 1, 3)])   # the Agda spelling, CS_13 as one atom
d.win(4, 6, [N, ('CS', 1, 3)])     # CS13 N -> N CS13 ({0,1,3})
d.comm(3)                          # CX12 N -> N CX12 (disjoint)
d.win(2, 4, [N, ('CSd', 2, 3)])    # CSd23 N -> N CSd23 ({0,2,3})
d.comm(1)                          # CX12 N -> N CX12
d.win(0, 2, [N, ('CS', 2, 3)])     # CS23 N -> N CS23
d.win(1, 6, [E])                   # fold the pieces back ({1,2,3})
L = d.done()

# Lemma 1: CZ_03 conjugates the Toffoli T = Toff(0;1,2) to T . CCZ_123,
# in the form T CZ_03 T = CCZ_123 CZ_03.
T = ('TOFF', 0, 1, 2); CZ = ('CZ', 0, 3); K, Kd = ('K', 0), ('Kd', 0); D = ('CCZ', 0, 1, 2)
d = Derivation('T-CZ03-T', [T, CZ, T], [E, CZ], L)
d.win(0, 1, [K, D, Kd])            # the Toffoli as K D K^-1 ({0,1,2})
d.win(4, 5, [K, D, Kd])
d.win(2, 5, [N])                   # K^-1 CZ_03 K = CX_30 ({0,3})
d.win(1, 1, [N, N])                # K (N N) D N D K^-1
d.delta(2)                         # K N (D CCZ312) D K^-1
d.lemma('CCZ312-CCZ012', 2, forward=False)   # D CCZ312 -> CCZ312 D ... we have D CCZ312: lemma is [a,b]->[b,a] with a = CCZ312, b = D; backwards: [b,a] -> [a,b]
d.win(3, 5, [])                    # D D = eps
d.win(2, 3, [E])                   # CCZ312 = CCZ123 (symmetry, {1,2,3})
d.lemma('CCZ123-CX30', 1, forward=False)      # N E -> E N
d.comm(0)                          # K E -> E K (disjoint)
d.win(1, 4, [CZ])                  # K N K^-1 = CZ_03
L = d.done()
print('lemmas:', list(L))

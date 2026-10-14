# The four-wire lemma library, in order: the hand derivations (lemmas4 ..
# lemmas8), the gadget forms at every target (gadgets4), and the
# commutation facts of the phase gadget found by the engine (passes)
# and the merge (lemmas10).
import lemmas8
import passes as P
from deriv import Derivation, show
from lemmas5 import T, C3, C3d, C2, C2d, PP3, PP2
from lemmas8 import L
import gadgets4
G = gadgets4.setup()
PPu = G[0]
FACTS = []
# same target, separated on one, two or three controls
for S in ([3], [2, 3], [1, 2, 3]):
    FACTS.append(P.prove([P.Col(S, PPu)], PPu))
# different targets 0 and 1, separated on wire 3 (or 2 and 3), crossing colours
for A, B in [(G[0], [P.Col([3], G[1])]), (G[0], [P.Col([2, 3], G[1])]),
             ([P.Col([1], G[0])], [P.Col([3], G[1])]), (G[0], [P.Col([0, 3], G[1])]),
             ([P.Col([1], G[0])], [P.Col([0, 3], G[1])])]:
    FACTS.append(P.prove(A, B))
import lemmas10
FACTS += ['merge3', 'adj01']

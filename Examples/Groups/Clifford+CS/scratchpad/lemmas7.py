# X on the target inverts the phase gadget and the rotation: the flipped
# gadgets of the decoding are the inverses (pp a (a+1) . pp (a+1) a = eps,
# the rule px-inv), from R0 and ROT^2 = E.
from deriv import Derivation, show, fp, cczs, norm
import lemmas6 as L6
from lemmas6 import (L, ensure_comm, ensure_pass, swap_adj, spell, supp, T, C3, C3d, D, Dp, E, F, K, Kd,
                     CS13, CZ13, PP3, PPi, ROT, c, cd, s, CX30, S3, S3d, CZ03)

X0 = ('X', 0)
CZ01, CX10, CZ23 = ('CZ', 0, 1), ('CX', 1, 0), ('CZ', 2, 3)

# X0 T X0 = T (X on the target of the Toffoli), X0 C3 X0 = S3 C3^-1
d = Derivation('PP-flip', [X0] + PP3 + [X0], PPi, L)
for k in (4, 3, 2): d.win(k, k, [X0, X0])               # (X0 T X0)(X0 C3 X0)(X0 T X0)(X0 C3d X0)
d.win(0, 3, [T]); d.win(1, 4, [S3, C3d]); d.win(3, 6, [T]); d.win(4, 7, [C3, S3d])
# T S3 C3d T C3 S3d: S3 to the right, cancelling
d.win(1, 3, [C3d, S3]); d.comm(2); d.win(3, 5, [C3, S3]); d.win(4, 6, [])   # T C3d T C3
d.lemma('C3-Ai', 0, forward=False)                                           # C3 T C3d T
L.update(d.done())

# X0 ROT X0 = ROT E
d = Derivation('X0-ROT', [X0] + ROT + [X0], ROT + [E], L)
d.lemma('ROT=[c,F]', 1)                                   # X0 c F cd F X0
for k in (4, 3, 2): d.win(k, k, [X0, X0])
d.win(0, 3, [c, CZ01, CX10]); d.win(3, 6, [F, CZ23]); d.win(5, 8, [CX10, CZ01, cd]); d.win(8, 11, [F, CZ23])
# c CZ01 CX10 F CZ23 CX10 CZ01 cd F CZ23
d.comm(4)                                                 # c CZ01 CX10 F CX10 CZ23 CZ01 cd F CZ23
d.delta(2)                                                # c CZ01 F E CZ23 CZ01 cd F CZ23
swap_adj(d, 1); swap_adj(d, 2); swap_adj(d, 3); d.win(4, 6, [])   # c F E CZ23 cd F CZ23
d.comm(3); d.lemma(ensure_pass(E, cd), 2)                 # c F cd E CZ23 F CZ23
swap_adj(d, 4); swap_adj(d, 3); d.win(5, 7, [])           # c F cd F E
d.lemma('ROT=[c,F]', 0, forward=False)
L.update(d.done())

d = Derivation('ROT-inv', ROT + [X0] + ROT + [X0], [], L)
d.lemma('X0-ROT', 15); d.lemma('ROT2=E', 0); d.win(0, 2, [])
L.update(d.done())
print('lemmas:', len(L))

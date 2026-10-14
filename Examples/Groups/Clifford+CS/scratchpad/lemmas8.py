# PP^4 = eps (pp-ord) and the symmetries of the gadgets under the swaps
# of their controls: Sw12 fixes PP letter by letter (the Toffoli is
# symmetric in its controls, CS03 does not see wires 1 2); Sw23 fixes
# ROT letter by letter (CCZ_023 is symmetric, CK10 does not see 2 3);
# Sw12 fixes ROT through its form as a conjugate of PP^-1, where
# Sw12 Sw13 = Sw13 Sw23 and Sw23 fixes PP.
from deriv import Derivation, show, fp, cczs, norm
import lemmas7 as L7
from lemmas7 import (L, ensure_comm, ensure_pass, swap_adj, T, C3, C3d, E, F, K, Kd, PP3, PPi, ROT, c, cd)
from lemmas6 import SW12, SW23, SW13w, U, Ui

d = Derivation('PP4', PP3 * 4, [], L)
d.lemma('PP2=E', 0); d.lemma('PP2=E', 1); d.win(0, 2, []); L.update(d.done())

d = Derivation('SW12-PP', [SW12] + PP3 + [SW12], PP3, L)
for k in (4, 3, 2): d.win(k, k, [SW12, SW12])
d.win(0, 3, [T]); d.comm(1); d.win(2, 4, []); d.win(2, 5, [T]); d.comm(3); d.win(4, 6, [])
L.update(d.done())

d = Derivation('SW23-ROT', [SW23] + ROT + [SW23], ROT, L)
d.lemma('ROT=[c,F]', 1)
for k in (4, 3, 2): d.win(k, k, [SW23, SW23])
d.comm(0); d.win(1, 3, []); d.win(1, 4, [F]); d.comm(2); d.win(3, 5, []); d.win(3, 6, [F])
d.lemma('ROT=[c,F]', 0, forward=False); L.update(d.done())

# PP^-1 = PP^3, so Sw23 fixes PP^-1 too
d = Derivation('PPi=PP3^3', PPi, PP3 * 3, L)
d.lemma('PP4', 4, forward=False); d.win(3, 5, []); d.win(2, 4, []); d.win(1, 3, []); d.win(0, 2, [])
L.update(d.done())

d = Derivation('S3i', [SW23] + PPi + [SW23], PPi, L)
d.lemma('PPi=PP3^3', 1); d.win(9, 9, [SW23, SW23]); d.win(5, 5, [SW23, SW23])
d.lemma('S3', 12); d.lemma('S3', 6); d.lemma('S3', 0); d.lemma('PPi=PP3^3', 0, forward=False)
L.update(d.done())

# Sw12 Sw13 = Sw13 Sw23 (a window on wires 1 2 3), Sw23 passes the wire-0 letters
d = Derivation('SW12-ROT', [SW12] + ROT + [SW12], ROT, L)
d.lemma('ROT=[c,F]', 1); d.lemma('ROT-form', 1)           # SW12 K SW13w U PPi Ui SW13w Kd SW12
d.comm(0); d.win(1, 5, SW13w + [SW23])                     # K SW13w SW23 U PPi Ui SW13w Kd SW12
d.comm(4); d.comm(5); d.comm(6)                            # K SW13w U SW23 PPi Ui SW13w Kd SW12
d.win(12, 12, [SW23, SW23]); d.lemma('S3i', 7)             # K SW13w U PPi SW23 Ui SW13w Kd SW12
d.comm(11); d.comm(12); d.comm(13)                         # K SW13w U PPi Ui SW23 SW13w Kd SW12
d.comm(18); d.win(17, 19, []); d.win(14, 17, SW13w)        # K SW13w U PPi Ui SW13w Kd
d.lemma('ROT-form', 0, forward=False); d.lemma('ROT=[c,F]', 0, forward=False)
L.update(d.done())
print('lemmas:', len(L))

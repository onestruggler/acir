/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The rules (1)–(7) are complete on one, two and three wires

Translation of `ThreeWire.agda`.  Two circuits over this folder's gates on
at most three wires that are the same function on states are equal by the
rules of `Theory`, and the circuits on one, two and three wires present S₂,
S₄ and S₈.  Each width is a Reidemeister–Schreier step from Symmetric's
presentation of the permutations of the states (`BySymmetric`), with the
Coxeter relations between the edge Toffolis and the gates' words derived
from the rules (`Width1`, `Width2`, `Width3`).  On three wires only the
rules (1)–(6) and the laws of the swap take part: rule (7) lives on four.

This is what a step on three wires of a four-wire derivation rests on
(`FourWire`'s `bot` and `top`).
-/
import QCert.Alt16RevCir.Width1
import QCert.Alt16RevCir.Width2
import QCert.Alt16RevCir.Width3

namespace QCert.Alt16RevCir.ThreeWire

export Width1 (complete₁ presentation₁ step₁)
export Width2 (complete₂ presentation₂ step₂)
export Width3 (complete₃ presentation₃ step₃)

end QCert.Alt16RevCir.ThreeWire

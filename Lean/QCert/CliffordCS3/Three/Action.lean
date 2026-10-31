/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The two-coset action for three-qubit Clifford+CS

The representatives are 1 and i_[7].  The macro atoms are Z = i_[7]
and K = K_[3,7].  A decoding supplies the seven Gray-path transpositions
and A = K_[3,7] Z⁻¹, together with the one-point sign Q = Z².
The phase P = i_[3] i_[7] is CS₁₂.

The equations verifying this action belong to the finite certificate;
no semantic equation is used as a syntactic axiom here.
-/
import QCert.CliffordCS3.Syntax
import QCert.CliffordCS3.Macro.Basic
import QCert.CliffordT2.ReidemeisterSchreier

namespace QCert.CliffordCS3.Three

open Macro

/-- Circuit words for the Gray-path transpositions, K_[3,7] Z⁻¹, and Z². -/
structure Decoding where
  token : Fin 7 → Word Gen
  atom : Word Gen
  zsign : Word Gen

/-- The two-point phase i_[3] i_[7]. -/
def phase : Word Gen := W.CS12

/-- The sign on point 7. -/
def sign (D : Decoding) : Word Gen := D.zsign

/-- The macro coset action; false names 1 and true names i_[7]. -/
def action (D : Decoding) : Bool → ML → Word Gen × Bool
  | c, .T d =>
    (if c && decide (d = 6) then phase * D.token d * sign D else D.token d, c)
  | false, .Z => (1, true)
  | true, .Z => (sign D, false)
  | false, .K => (D.atom, true)
  | true, .K => (D.atom ^ 2 * phase, false)

end QCert.CliffordCS3.Three

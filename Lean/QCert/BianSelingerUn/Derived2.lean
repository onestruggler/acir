/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: derived relations for Case 3

Conjugation by `X_[j,ℓ]` exchanges `j` and `ℓ` (from (2), (10), (11),
(13), (14)), whence the relations (24) and (25) of Figure 2 and the
commutation of a syllable with the swap of two indices it moves.
-/
import QCert.BianSelingerUn.Derived

namespace QCert.BianSelingerUn

variable {n : ℕ}

/-- If `x² = 1` and `x a = b x`, then `x b = a x`. -/
theorem semiconj_swap {M : Type*} [Monoid M] {x a b : M} (hx : x * x = 1)
    (h : SemiconjBy x a b) : SemiconjBy x b a := by
  unfold SemiconjBy at h ⊢
  calc x * b = x * (b * (x * x)) := by rw [hx, mul_one]
    _ = x * (x * a) * x := by rw [← mul_assoc b, ← h]; simp only [mul_assoc]
    _ = a * x := by rw [← mul_assoc, hx, one_mul]

section Swap

variable (j l : Fin n) (h : j < l)

/-- `X_[j,ℓ] i_[j] = i_[ℓ] X_[j,ℓ]`. -/
theorem sc_Xi : SemiconjBy (gX j l h) (gi j) (gi l) := (e10 j l h).symm

/-- `X_[j,ℓ] i_[ℓ] = i_[j] X_[j,ℓ]`. -/
theorem sc_Xi' : SemiconjBy (gX j l h) (gi l) (gi j) :=
  semiconj_swap (e2 j l h) (sc_Xi j l h)

end Swap

/-- `X_[k,ℓ] K_[j,k] = K_[j,ℓ] X_[k,ℓ]` (`j < k < ℓ`), from (14). -/
theorem sc_XK_low (j k l : Fin n) (hjk : j < k) (hkl : k < l) :
    SemiconjBy (gX k l hkl) (gK j k hjk) (gK j l (hjk.trans hkl)) := (e14 j k l hjk hkl).symm

theorem sc_XK_low' (j k l : Fin n) (hjk : j < k) (hkl : k < l) :
    SemiconjBy (gX k l hkl) (gK j l (hjk.trans hkl)) (gK j k hjk) :=
  semiconj_swap (e2 k l hkl) (sc_XK_low j k l hjk hkl)

/-- `X_[j,k] K_[j,ℓ] = K_[k,ℓ] X_[j,k]` (`j < k < ℓ`), from (13). -/
theorem sc_XK_high (j k l : Fin n) (hjk : j < k) (hkl : k < l) :
    SemiconjBy (gX j k hjk) (gK j l (hjk.trans hkl)) (gK k l hkl) := (e13 j k l hjk hkl).symm

theorem sc_XK_high' (j k l : Fin n) (hjk : j < k) (hkl : k < l) :
    SemiconjBy (gX j k hjk) (gK k l hkl) (gK j l (hjk.trans hkl)) :=
  semiconj_swap (e2 j k hjk) (sc_XK_high j k l hjk hkl)

/-- `X_[k,ℓ] X_[j,k] = X_[j,k] X_[j,ℓ]` (`j < k < ℓ`), (11). -/
theorem sc_XX (j k l : Fin n) (hjk : j < k) (hkl : k < l) :
    SemiconjBy (gX j k hjk) (gX j l (hjk.trans hkl)) (gX k l hkl) := (e11 j k l hjk hkl).symm

theorem sc_XX' (j k l : Fin n) (hjk : j < k) (hkl : k < l) :
    SemiconjBy (gX j k hjk) (gX k l hkl) (gX j l (hjk.trans hkl)) :=
  semiconj_swap (e2 j k hjk) (sc_XX j k l hjk hkl)

/-- (24): `X_[j,ℓ] i_[j]^e X_[k,ℓ] ∼ X_[j,k] X_[j,ℓ] i_[j]^e` (`j < k < ℓ`). -/
theorem f24 (j k l : Fin n) (hjk : j < k) (hkl : k < l) (e : ℕ) :
    gX j l (hjk.trans hkl) * gi j ^ e * gX k l hkl =
      gX j k hjk * gX j l (hjk.trans hkl) * gi j ^ e := by
  have hc : Commute (gi j) (gX k l hkl) := e5 j k l hkl hjk.ne (hjk.trans hkl).ne
  conv_lhs => rw [mul_assoc, (hc.pow_left e).eq, ← mul_assoc, e12 j k l hjk hkl, e11 j k l hjk hkl]

end QCert.BianSelingerUn

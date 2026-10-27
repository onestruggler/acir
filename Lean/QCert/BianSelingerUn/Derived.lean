/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: derived relations (Figure 2)

The relations of Figure 2 used in the proof of the Main Lemma, derived from
Figure 1 in the presented monoid `Pres n` (the paper calls their proofs
"straightforward").  `K† = K⁷`.  For indices `j < ℓ` write `a = i_[j]`,
`b = i_[ℓ]`, `x = X_[j,ℓ]`, `k = K_[j,ℓ]`; the derivations rest on

* `k⁷ = a b k` (from (3), (17), (18)), so `k⁷` is the inverse of `k`;
* `x a = b x`, `x b = a x` (from (2), (10)); `x k = k b²` (from (15));
* `k b³ = b k b k` (16) and `k a b = a b k` (17).

Everything is stated with a tail `t`, products associated to the right, so
that the equations rewrite inside longer words.
-/
import QCert.BianSelingerUn.Pres

namespace QCert.BianSelingerUn

variable {n : ℕ}

section Diagonal

variable (j l : Fin n)

/-- `b a = a b`, from (4). -/
theorem t4 (hjl : j ≠ l) (t : Pres n) : gi l * (gi j * t) = gi j * (gi l * t) := by
  rw [← mul_assoc, ← e4 j l hjl, mul_assoc]

theorem ti4 (t : Pres n) : gi j * (gi j * (gi j * (gi j * t))) = t := by
  have := e1 j
  rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_one] at this
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, this, one_mul]

end Diagonal

section TwoIndices

variable (j l : Fin n) (h : j < l)

/-- (2) in tail form. -/
theorem tX2 (t : Pres n) : gX j l h * (gX j l h * t) = t := by
  rw [← mul_assoc, e2, one_mul]

/-- `x a = b x`. -/
theorem tXa (t : Pres n) : gX j l h * (gi j * t) = gi l * (gX j l h * t) := by
  have ha : gi j * t = gX j l h * (gi l * (gX j l h * t)) := by
    rw [← mul_assoc (gi l), e10, mul_assoc, tX2]
  rw [ha, tX2]

/-- `x b = a x`. -/
theorem tXb (t : Pres n) : gX j l h * (gi l * t) = gi j * (gX j l h * t) := by
  calc gX j l h * (gi l * t) = gX j l h * (gi l * (gX j l h * (gX j l h * t))) := by rw [tX2]
    _ = gX j l h * (gX j l h * (gi j * (gX j l h * t))) := by
        rw [← mul_assoc (gi l), e10, mul_assoc]
    _ = gi j * (gX j l h * t) := by rw [tX2]

/-- `b x = x a`, (10) in tail form. -/
theorem t10 (t : Pres n) : gi l * (gX j l h * t) = gX j l h * (gi j * t) := by
  rw [← mul_assoc, e10, mul_assoc]

/-- `x k = k b²`, from (15). -/
theorem tXK (t : Pres n) : gX j l h * (gK j l h * t) = gK j l h * (gi l * (gi l * t)) := by
  rw [← mul_assoc, ← e15 j l h, pow_two, mul_assoc, mul_assoc]

/-- (16) in tail form: `k b³ = b k b k`. -/
theorem t16 (t : Pres n) :
    gK j l h * (gi l * (gi l * (gi l * t))) = gi l * (gK j l h * (gi l * (gK j l h * t))) := by
  have e := e16 j l h
  rw [pow_three] at e
  calc gK j l h * (gi l * (gi l * (gi l * t))) = gK j l h * (gi l * (gi l * gi l)) * t := by
        simp only [mul_assoc]
    _ = _ := by rw [e]; simp only [mul_assoc]

/-- (17) in tail form: `a b k = k a b`. -/
theorem t17 (t : Pres n) : gi j * (gi l * (gK j l h * t)) = gK j l h * (gi j * (gi l * t)) := by
  have e := e17 j l h
  calc gi j * (gi l * (gK j l h * t)) = gi j * gi l * gK j l h * t := by simp only [mul_assoc]
    _ = _ := by rw [← e]; simp only [mul_assoc]

/-- (18) in tail form: `k k a b = 1`. -/
theorem t18 (t : Pres n) : gK j l h * (gK j l h * (gi j * (gi l * t))) = t := by
  have e := e18 j l h
  rw [pow_two] at e
  calc gK j l h * (gK j l h * (gi j * (gi l * t))) = gK j l h * gK j l h * gi j * gi l * t := by
        simp only [mul_assoc]
    _ = t := by rw [e, one_mul]

/-- `K† = a b k`, from (3), (17), (18). -/
theorem tKd (t : Pres n) : gK j l h ^ 7 * t = gi j * (gi l * (gK j l h * t)) := by
  have e3' := e3 j l h
  rw [show (8 : ℕ) = 1 + 7 from rfl, pow_add, pow_one] at e3'
  calc gK j l h ^ 7 * t = gK j l h ^ 7 * (gK j l h * (gK j l h * (gi j * (gi l * t)))) := by
        rw [t18]
    _ = (gK j l h * gK j l h ^ 7) * (gK j l h * (gi j * (gi l * t))) := by
        rw [← mul_assoc, ← pow_succ, pow_succ']
    _ = gK j l h * (gi j * (gi l * t)) := by rw [e3', one_mul]
    _ = _ := by rw [t17]

theorem tKKd (t : Pres n) : gK j l h * (gK j l h ^ 7 * t) = t := by
  rw [← mul_assoc, ← pow_succ', e3, one_mul]

theorem tKdK (t : Pres n) : gK j l h ^ 7 * (gK j l h * t) = t := by
  rw [← mul_assoc, ← pow_succ, e3, one_mul]

/-- `k a = a b k b³`, from (17). -/
theorem tKa (t : Pres n) :
    gK j l h * (gi j * t) = gi j * (gi l * (gK j l h * (gi l * (gi l * (gi l * t))))) := by
  rw [t17, ti4]

/-- `k k = a³ b³`, from (18). -/
theorem tKK (t : Pres n) :
    gK j l h * (gK j l h * t) =
      gi j * (gi j * (gi j * (gi l * (gi l * (gi l * t))))) := by
  have ident : gi j * (gi l * (gi j * (gi j * (gi j * (gi l * (gi l * (gi l * t))))))) = t := by
    rw [t4 j l h.ne, t4 j l h.ne, t4 j l h.ne, ti4, ti4]
  conv_lhs => rw [← ident]
  rw [t18]

/-- `k x = b² k`. -/
theorem tKX (t : Pres n) : gK j l h * (gX j l h * t) = gi l * (gi l * (gK j l h * t)) := by
  conv_lhs => rw [← tKKd j l h t]
  rw [tXK, tKK, ti4 l, tKd, t4 j l h.ne, ti4]

/-- `x a b k b = k a`. -/
theorem xabkb (t : Pres n) :
    gX j l h * (gi j * (gi l * (gK j l h * (gi l * t)))) = gK j l h * (gi j * t) := by
  rw [tXa, tXb, tXK, t16, t4 j l h.ne, ← t16, t17, ti4 l]

/-- Figure 2, (21): `K†_[j,ℓ] i_[j] ∼ i_[j] i_[ℓ] X_[j,ℓ] K†_[j,ℓ] i_[ℓ]`. -/
theorem f21 (t : Pres n) :
    gK j l h ^ 7 * (gi j * t) = gi j * (gi l * (gX j l h * (gK j l h ^ 7 * (gi l * t)))) := by
  rw [tKd, tKd, xabkb]

/-- Figure 2, (22): `K_[j,ℓ] ∼ i_[j]³ i_[ℓ]³ K†_[j,ℓ]`. -/
theorem f22 (t : Pres n) :
    gK j l h * t = gi j * (gi j * (gi j * (gi l * (gi l * (gi l * (gK j l h ^ 7 * t)))))) := by
  rw [tKd, t4 j l h.ne, t4 j l h.ne, t4 j l h.ne, ti4, ti4]

/-- Figure 2, (23): `K†_[j,ℓ] i_[ℓ] K_[j,ℓ] ∼ i_[ℓ]³ X_[j,ℓ] K†_[j,ℓ] i_[ℓ]`. -/
theorem f23 (t : Pres n) :
    gK j l h ^ 7 * (gi l * (gK j l h * t)) =
      gi l * (gi l * (gi l * (gX j l h * (gK j l h ^ 7 * (gi l * t))))) := by
  rw [tKd, tKd, xabkb, tKa, t4 j l h.ne, t4 j l h.ne, t4 j l h.ne, ti4 l, ← t16]

/-- Figure 2, (28): `K†_[j,ℓ] i_[ℓ] X_[j,ℓ] ∼ X_[j,ℓ] i_[j]³ i_[ℓ] K†_[j,ℓ] i_[ℓ]`. -/
theorem f28 (t : Pres n) :
    gK j l h ^ 7 * (gi l * (gX j l h * t)) =
      gX j l h * (gi j * (gi j * (gi j * (gi l * (gK j l h ^ 7 * (gi l * t)))))) := by
  rw [tKd, tKd, t10, tKX, tKa, t4 j l h.ne, t4 j l h.ne, t4 j l h.ne, ti4 l, t4 j l h.ne,
    ti4 j, tXb, tXb, tXK]

/-- (17) for `K†`: `K† b a = a b K†`. -/
theorem f17 (t : Pres n) :
    gK j l h ^ 7 * (gi l * (gi j * t)) = gi j * (gi l * (gK j l h ^ 7 * t)) := by
  conv_lhs => rw [tKd, t4 j l h.ne, ← t17]
  rw [tKd]

/-- The inverse of (15): `K†_[j,ℓ] X_[j,ℓ] ∼ i_[ℓ]² K†_[j,ℓ]`. -/
theorem f15' (t : Pres n) :
    gK j l h ^ 7 * (gX j l h * t) = gi l * (gi l * (gK j l h ^ 7 * t)) := by
  rw [tKd, tKd, tKX, t4 j l h.ne, t4 j l h.ne]

end TwoIndices

end QCert.BianSelingerUn

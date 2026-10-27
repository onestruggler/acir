/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: the derived equations of Table 3.2

Lemma 24: the equations (21)–(32) of Table 3.2 follow from those of
Table 3.1.  They are stated in the presented monoid `Pres n`, at symbolic
indices; the thesis states (31) and (32) at the indices `1, 2, 3, 4`, here
they hold at any `j < k < ℓ < t`.  Equations (28)–(30), and (18) read
through (23), are the instances `e = 3, 2, 1, 0` of one equation
`H_[j,k] ω^e_[j] X_[j,k] ≈ ω^{4+e}_[j] ω^e_[k] X_[j,k] H_[j,k] ω^{4-e}_[j]`
(`eHωX`), proved once as in the thesis.

Also: the commutations of powers of `ω` used throughout, the equation
`H_[j,k] ω⁴_[j] ≈ ω⁴_[j] ω⁴_[k] X_[j,k] H_[j,k]` (`eH4`), and the
relabelling of generators by conjugation with `X_[a,a+1]`.
-/
import QCert.Greylyn.Pres

namespace QCert.Greylyn

variable {n : ℕ}

section Monoid

variable {M : Type*} [Monoid M]

/-- `x a = b x` with `x² = 1` gives `a x = x b`. -/
theorem conj_swap {a b x : M} (hx : x * x = 1) (h : x * a = b * x) : a * x = x * b := by
  calc a * x = x * x * a * x := by rw [hx, one_mul]
    _ = x * (x * a) * x := by rw [mul_assoc x x a]
    _ = x * (b * x) * x := by rw [h]
    _ = x * b * (x * x) := by simp only [mul_assoc]
    _ = x * b := by rw [hx, mul_one]

/-- `x a = b x` with `x² = 1` gives `x a x = b`. -/
theorem conj_eq {a b x : M} (hx : x * x = 1) (h : x * a = b * x) : x * a * x = b := by
  rw [h, mul_assoc, hx, mul_one]

/-- `a x = x b` with `x² = 1` gives `x a = b x`. -/
theorem conj_swap' {a b x : M} (hx : x * x = 1) (h : a * x = x * b) : x * a = b * x := by
  calc x * a = x * a * (x * x) := by rw [hx, mul_one]
    _ = x * (a * x) * x := by simp only [mul_assoc]
    _ = x * (x * b) * x := by rw [h]
    _ = (x * x) * (b * x) := by simp only [mul_assoc]
    _ = b * x := by rw [hx, one_mul]

/-- Conjugating a product of five letters letter by letter. -/
theorem conj_five {y a b c d e a' b' c' d' e' : M} (hy : y * y = 1) (ha : y * a = a' * y)
    (hb : y * b = b' * y) (hc : y * c = c' * y) (hd : y * d = d' * y) (he : y * e = e' * y) :
    y * (a * b * c * d * e) * y = a' * b' * c' * d' * e' := by
  calc y * (a * b * c * d * e) * y = y * a * b * c * d * e * y := by simp only [mul_assoc]
    _ = a' * (y * b) * c * d * e * y := by rw [ha]; simp only [mul_assoc]
    _ = a' * b' * (y * c) * d * e * y := by rw [hb]; simp only [mul_assoc]
    _ = a' * b' * c' * (y * d) * e * y := by rw [hc]; simp only [mul_assoc]
    _ = a' * b' * c' * d' * (y * e) * y := by rw [hd]; simp only [mul_assoc]
    _ = a' * b' * c' * d' * e' * (y * y) := by rw [he]; simp only [mul_assoc]
    _ = a' * b' * c' * d' * e' := by rw [hy, mul_one]

/-- A two-letter relation with a tail. -/
theorem tl {a b c d : M} (h : a * b = c * d) (w : M) : a * (b * w) = c * (d * w) := by
  rw [← mul_assoc, h, mul_assoc]

/-- A product `a b` commuting with `c`, with a tail. -/
theorem comm2_tail {a b c : M} (h : Commute (a * b) c) (w : M) :
    c * (a * (b * w)) = a * (b * (c * w)) := by
  calc c * (a * (b * w)) = c * (a * b) * w := by simp only [mul_assoc]
    _ = a * b * c * w := by rw [← h.eq]
    _ = a * (b * (c * w)) := by simp only [mul_assoc]

end Monoid

section Basic

variable {j k l : Fin n}

theorem gX_sq (h : j < k) : gX j k h * gX j k h = 1 := e3 j k h
theorem gH_sq (h : j < k) : gH j k h * gH j k h = 1 := e2 j k h

theorem gω_pow_eight (j : Fin n) : gω j ^ 8 = 1 := e1 j

theorem gω_pow_add_eight (j : Fin n) (a : ℕ) : gω j ^ (a + 8) = gω j ^ a := by
  rw [pow_add, e1, mul_one]

theorem gω_pow_mul_pow_eq_one (j : Fin n) {a b : ℕ} (h : a + b = 8) :
    gω j ^ a * gω j ^ b = 1 := by
  rw [← pow_add, h, e1]

theorem c_ωω (h : j ≠ k) : Commute (gω j) (gω k) := e4 j k h

theorem c_ωωpow (h : j ≠ k) (a b : ℕ) : Commute (gω j ^ a) (gω k ^ b) :=
  ((c_ωω h).pow_left a).pow_right b

theorem c_ωH (hjk : j < k) (hlj : l ≠ j) (hlk : l ≠ k) : Commute (gω l) (gH j k hjk) :=
  e5 j k l hjk hlj hlk

theorem c_ωX (hjk : j < k) (hlj : l ≠ j) (hlk : l ≠ k) : Commute (gω l) (gX j k hjk) :=
  e6 j k l hjk hlj hlk

/-- (10) as a semiconjugation: `X_[j,k] ω_[k] = ω_[j] X_[j,k]`. -/
theorem s_Xωk (h : j < k) : SemiconjBy (gX j k h) (gω k) (gω j) := e10 j k h

/-- (11) as a semiconjugation: `X_[j,k] ω_[j] = ω_[k] X_[j,k]`. -/
theorem s_Xωj (h : j < k) : SemiconjBy (gX j k h) (gω j) (gω k) := e11 j k h

theorem c_ω2H (h : j < k) : Commute (gω j * gω k) (gH j k h) := by
  show gω j * gω k * gH j k h = gH j k h * (gω j * gω k)
  rw [e17, mul_assoc]

theorem c_ω2X (h : j < k) : Commute (gω j * gω k) (gX j k h) := by
  show gω j * gω k * gX j k h = gX j k h * (gω j * gω k)
  rw [e16, mul_assoc]

/-- `ω^e_[j] ω^e_[k]` commutes with `H_[j,k]`, from (17). -/
theorem c_ω2Hpow (h : j < k) (e : ℕ) : Commute (gω j ^ e * gω k ^ e) (gH j k h) := by
  rw [← (c_ωω h.ne).mul_pow]; exact (c_ω2H h).pow_left e

/-- `ω^e_[j] ω^e_[k]` commutes with `X_[j,k]`, from (16). -/
theorem c_ω2Xpow (h : j < k) (e : ℕ) : Commute (gω j ^ e * gω k ^ e) (gX j k h) := by
  rw [← (c_ωω h.ne).mul_pow]; exact (c_ω2X h).pow_left e

end Basic

/-! ### Table 3.2 -/

section Table32

variable (j k l t : Fin n)

/-- (21) `H_[j,ℓ] X_[j,k] ≈ X_[j,k] H_[k,ℓ]` (`j < k < ℓ`). -/
theorem e21 (hjk : j < k) (hkl : k < l) :
    gH j l (hjk.trans hkl) * gX j k hjk = gX j k hjk * gH k l hkl :=
  conj_swap (e3 j k hjk) (e14 j k l hjk hkl)

/-- (22) `H_[ℓ,j] X_[j,k] ≈ X_[j,k] H_[ℓ,k]` (`ℓ < j < k`). -/
theorem e22 (hlj : l < j) (hjk : j < k) :
    gH l j hlj * gX j k hjk = gX j k hjk * gH l k (hlj.trans hjk) :=
  conj_swap (e3 j k hjk) (e15 j k l hlj hjk)

/-- (23) `X_[j,k] H_[j,k] ≈ H_[j,k] ω⁴_[k]` (`j < k`). -/
theorem e23 (h : j < k) : gX j k h * gH j k h = gH j k h * gω k ^ 4 :=
  conj_swap (e2 j k h) (e18 j k h)

/-- (24) `ω²_[j] H_[j,k] ≈ ω⁶_[k] H_[j,k] ω²_[k] ω²_[j]` (`j < k`). -/
theorem e24 (h : j < k) :
    gω j ^ 2 * gH j k h = gω k ^ 6 * gH j k h * gω k ^ 2 * gω j ^ 2 := by
  have hc : gω k ^ 2 * gω j ^ 2 = gω j ^ 2 * gω k ^ 2 := (c_ωωpow h.ne' 2 2).eq
  calc gω j ^ 2 * gH j k h = gω k ^ 6 * gω k ^ 2 * (gω j ^ 2 * gH j k h) := by
        rw [gω_pow_mul_pow_eq_one k (a := 6) (b := 2) rfl, one_mul]
    _ = gω k ^ 6 * ((gω k ^ 2 * gω j ^ 2) * gH j k h) := by simp only [mul_assoc]
    _ = gω k ^ 6 * (gH j k h * (gω j ^ 2 * gω k ^ 2)) := by rw [hc, (c_ω2Hpow h 2).eq]
    _ = gω k ^ 6 * gH j k h * gω k ^ 2 * gω j ^ 2 := by rw [← hc]; simp only [mul_assoc]

/-- (25) `X_[j,ℓ] H_[k,ℓ] ≈ H_[j,k] ω⁴_[k] X_[j,k] X_[j,ℓ]` (`j < k < ℓ`). -/
theorem e25 (hjk : j < k) (hkl : k < l) :
    gX j l (hjk.trans hkl) * gH k l hkl =
      gH j k hjk * gω k ^ 4 * gX j k hjk * gX j l (hjk.trans hkl) := by
  calc gX j l (hjk.trans hkl) * gH k l hkl
        = gX j k hjk * (gX j k hjk * gX j l (hjk.trans hkl)) * gH k l hkl := by
          rw [← mul_assoc, gX_sq, one_mul]
    _ = gX j k hjk * gX k l hkl * (gX j k hjk * gH k l hkl) := by
          rw [e12 j k l hjk hkl]; simp only [mul_assoc]
    _ = gX j k hjk * (gX k l hkl * gH j l (hjk.trans hkl)) * gX j k hjk := by
          rw [← e21 j k l hjk hkl]; simp only [mul_assoc]
    _ = gX j k hjk * gH j k hjk * (gX k l hkl * gX j k hjk) := by
          rw [← e22 k l j hjk hkl]; simp only [mul_assoc]
    _ = gX j k hjk * gH j k hjk * gX j k hjk * gX j l (hjk.trans hkl) := by
          rw [← e12 j k l hjk hkl]; simp only [mul_assoc]
    _ = gH j k hjk * gω k ^ 4 * gX j k hjk * gX j l (hjk.trans hkl) := by rw [e23]

/-- `X_[j,k] H_[j,k] ω⁴_[k] ≈ H_[j,k]`, from (23). -/
theorem eXH4 (h : j < k) : gX j k h * gH j k h * gω k ^ 4 = gH j k h := by
  rw [mul_assoc, ← e23, ← mul_assoc, gX_sq, one_mul]

/-- (26) `H_[j,k] ω²_[j] H_[j,k] ≈ X_[j,k] ω⁷_[k] ω_[j] H_[j,k] ω²_[j]` (`j < k`). -/
theorem e26 (h : j < k) :
    gH j k h * gω j ^ 2 * gH j k h =
      gX j k h * gω k ^ 7 * gω j * gH j k h * gω j ^ 2 := by
  have h35 : gω j ^ 3 * gω k ^ 5 = gω j * gω k * (gω j ^ 2 * gω k ^ 4) := by
    rw [show gω j ^ 3 = gω j * gω j ^ 2 from pow_succ' _ 2,
      show gω k ^ 5 = gω k * gω k ^ 4 from pow_succ' _ 4]
    simp only [mul_assoc]
    rw [((c_ωω h.ne).pow_left 2).left_comm]
  have hX : gX j k h * gω k ^ 7 * gω j = gω j ^ 7 * gω k * gX j k h := by
    rw [((s_Xωk h).pow_right 7).eq]
    simp only [mul_assoc]
    rw [(s_Xωj h).eq]
  calc gH j k h * gω j ^ 2 * gH j k h = gω j ^ 6 * gH j k h * gω j ^ 3 * gω k ^ 5 := e19 j k h
    _ = gω j ^ 6 * gH j k h * (gω j * gω k * (gω j ^ 2 * gω k ^ 4)) := by
          rw [← h35]; simp only [mul_assoc]
    _ = gω j ^ 6 * (gω j * gω k * gH j k h) * (gω j ^ 2 * gω k ^ 4) := by
          rw [(c_ω2H h).eq]; simp only [mul_assoc]
    _ = gω j ^ 6 * gω j * gω k * (gH j k h * gω k ^ 4 * gω j ^ 2) := by
          rw [(c_ωωpow h.ne 2 4).eq]; simp only [mul_assoc]
    _ = gω j ^ 6 * gω j * gω k * (gX j k h * gH j k h * gω j ^ 2) := by rw [← e23]
    _ = gω j ^ 7 * gω k * gX j k h * gH j k h * gω j ^ 2 := by
          rw [← pow_succ]; simp only [mul_assoc]
    _ = gX j k h * gω k ^ 7 * gω j * gH j k h * gω j ^ 2 := by rw [hX]

/-- (27) `H_[j,k] ω_[j] X_[j,k] ≈ ω_[j] ω⁵_[k] H_[j,k] ω⁷_[j]` (`j < k`). -/
theorem e27 (h : j < k) :
    gH j k h * gω j * gX j k h = gω j * gω k ^ 5 * gH j k h * gω j ^ 7 := by
  have hk : gω j * gω k * gω j ^ 7 = gω k := by
    rw [(c_ωω h.ne).eq, mul_assoc, ← pow_succ', show gω j ^ (7 + 1) = 1 from e1 j, mul_one]
  have h4 : gω k ^ 4 * gω j = gω j * gω k ^ 4 := ((c_ωω h.ne).pow_right 4).eq.symm
  calc gH j k h * gω j * gX j k h = gH j k h * gX j k h * gω k := by
        rw [mul_assoc, ← (s_Xωk h).eq, ← mul_assoc]
    _ = gω k ^ 4 * gH j k h * (gω j * gω k * gω j ^ 7) := by rw [e18, hk]
    _ = gω k ^ 4 * (gω j * gω k * gH j k h) * gω j ^ 7 := by
        rw [(c_ω2H h).eq]; simp only [mul_assoc]
    _ = (gω k ^ 4 * gω j) * gω k * gH j k h * gω j ^ 7 := by simp only [mul_assoc]
    _ = gω j * (gω k ^ 4 * gω k) * gH j k h * gω j ^ 7 := by rw [h4]; simp only [mul_assoc]
    _ = gω j * gω k ^ 5 * gH j k h * gω j ^ 7 := by rw [← pow_succ]

/-- The common form of (18), (28), (29) and (30):
`H_[j,k] ω^e_[j] X_[j,k] ≈ ω^{4+e}_[j] ω^e_[k] X_[j,k] H_[j,k] ω^{4-e}_[j]`
(`e ≤ 4`), by the derivation of the thesis' proofs of (28)–(30). -/
theorem eHωX (h : j < k) (e : ℕ) (he : e ≤ 4) :
    gH j k h * gω j ^ e * gX j k h =
      gω j ^ (4 + e) * gω k ^ e * gX j k h * gH j k h * gω j ^ (4 - e) := by
  have hj : gω j ^ (4 + e) * (gω k ^ (4 + e) * gω j ^ (4 - e)) = gω k ^ (4 + e) := by
    rw [(c_ωωpow h.ne (4 + e) (4 + e)).left_comm,
      gω_pow_mul_pow_eq_one j (a := 4 + e) (b := 4 - e) (by omega), mul_one]
  calc gH j k h * gω j ^ e * gX j k h = gH j k h * gX j k h * gω k ^ e := by
        rw [mul_assoc, ← ((s_Xωk h).pow_right e).eq, ← mul_assoc]
    _ = gω k ^ 4 * (gX j k h * gH j k h * gω k ^ 4) * gω k ^ e := by rw [e18, eXH4]
    _ = gω k ^ 4 * (gX j k h * (gH j k h * gω k ^ (4 + e))) := by
        rw [pow_add]; simp only [mul_assoc]
    _ = gω k ^ 4 * (gX j k h * (gH j k h * (gω j ^ (4 + e) * (gω k ^ (4 + e) *
          gω j ^ (4 - e))))) := by rw [hj]
    _ = gω k ^ 4 * (gX j k h * (gω j ^ (4 + e) * (gω k ^ (4 + e) * (gH j k h *
          gω j ^ (4 - e))))) := by rw [comm2_tail (c_ω2Hpow h (4 + e))]
    _ = gω k ^ 4 * (gω j ^ (4 + e) * (gω k ^ (4 + e) * (gX j k h * (gH j k h *
          gω j ^ (4 - e))))) := by rw [comm2_tail (c_ω2Xpow h (4 + e))]
    _ = gω j ^ (4 + e) * (gω k ^ e * (gX j k h * (gH j k h * gω j ^ (4 - e)))) := by
        rw [((c_ωωpow h.ne (4 + e) 4).symm).left_comm, ← mul_assoc (gω k ^ 4) (gω k ^ (4 + e)),
          ← pow_add, show 4 + (4 + e) = e + 8 by omega, gω_pow_add_eight]
    _ = gω j ^ (4 + e) * gω k ^ e * gX j k h * gH j k h * gω j ^ (4 - e) := by
        simp only [mul_assoc]

/-- (28) `H_[j,k] ω³_[j] X_[j,k] ≈ ω⁷_[j] ω³_[k] X_[j,k] H_[j,k] ω_[j]` (`j < k`). -/
theorem e28 (h : j < k) :
    gH j k h * gω j ^ 3 * gX j k h = gω j ^ 7 * gω k ^ 3 * gX j k h * gH j k h * gω j := by
  have := eHωX j k h 3 (by omega)
  rw [show 4 + 3 = 7 from rfl, show 4 - 3 = 1 from rfl, pow_one] at this
  exact this

/-- (29) `H_[j,k] ω²_[j] X_[j,k] ≈ ω⁶_[j] ω²_[k] X_[j,k] H_[j,k] ω²_[j]` (`j < k`). -/
theorem e29 (h : j < k) :
    gH j k h * gω j ^ 2 * gX j k h = gω j ^ 6 * gω k ^ 2 * gX j k h * gH j k h * gω j ^ 2 :=
  eHωX j k h 2 (by omega)

/-- (30) `H_[j,k] ω_[j] X_[j,k] ≈ ω⁵_[j] ω_[k] X_[j,k] H_[j,k] ω³_[j]` (`j < k`). -/
theorem e30 (h : j < k) :
    gH j k h * gω j * gX j k h = gω j ^ 5 * gω k * gX j k h * gH j k h * gω j ^ 3 := by
  have := eHωX j k h 1 (by omega)
  rw [show 4 + 1 = 5 from rfl, show 4 - 1 = 3 from rfl, pow_one, pow_one] at this
  exact this

/-- (31) `H_[ℓ,t] H_[j,k] X_[k,ℓ] H_[j,k] H_[ℓ,t] ≈ H_[j,ℓ] H_[k,t] X_[k,ℓ] H_[k,t] H_[j,ℓ]`
(`j < k < ℓ < t`; the thesis states it at `1, 2, 3, 4`). -/
theorem e31 (hjk : j < k) (hkl : k < l) (hlt : l < t) :
    gH l t hlt * gH j k hjk * gX k l hkl * gH j k hjk * gH l t hlt =
      gH j l (hjk.trans hkl) * gH k t (hkl.trans hlt) * gX k l hkl *
        gH k t (hkl.trans hlt) * gH j l (hjk.trans hkl) := by
  have hjl := hjk.trans hkl
  have hkt := hkl.trans hlt
  have ha : gX k l hkl * gH j k hjk = gH j l hjl * gX k l hkl := e15 k l j hjk hkl
  have hb : gX k l hkl * gH l t hlt = gH k t hkt * gX k l hkl := (e21 k l t hkl hlt).symm
  have hc : gH l t hlt * gH j k hjk = gH j k hjk * gH l t hlt :=
    (e7 j k l t hjk hlt (hjl.ne') (hkl.ne') (hjl.trans hlt).ne' hkt.ne').symm
  have he : gH l t hlt * gX k l hkl = gX k l hkl * gH k t hkt := (e14 k l t hkl hlt).symm
  have hf : gH j k hjk * gX k l hkl = gX k l hkl * gH j l hjl := e22 k l j hjk hkl
  have hg : gH j l hjl * gH k t hkt = gH k t hkt * gH j l hjl :=
    e7 j l k t hjl hkt hjk.ne' hkl.ne (hjl.trans hlt).ne' hlt.ne'
  calc gH l t hlt * gH j k hjk * gX k l hkl * gH j k hjk * gH l t hlt
        = gH l t hlt * gH j k hjk * (gX k l hkl * gH j k hjk) * gH l t hlt := by
          simp only [mul_assoc]
    _ = gH l t hlt * gH j k hjk * gH j l hjl * (gX k l hkl * gH l t hlt) := by
          rw [ha]; simp only [mul_assoc]
    _ = gH l t hlt * gH j k hjk * gH j l hjl * gH k t hkt * gX k l hkl := by
          rw [hb]; simp only [mul_assoc]
    _ = gH j k hjk * gH l t hlt * gH j l hjl * gH k t hkt * gX k l hkl := by rw [hc]
    _ = gH j l hjl * gH k t hkt * gH j k hjk * (gH l t hlt * gX k l hkl) := by
          rw [e20 j k l t hjk hkl hlt]; simp only [mul_assoc]
    _ = gH j l hjl * gH k t hkt * (gH j k hjk * gX k l hkl) * gH k t hkt := by
          rw [he]; simp only [mul_assoc]
    _ = gH j l hjl * gH k t hkt * gX k l hkl * (gH j l hjl * gH k t hkt) := by
          rw [hf]; simp only [mul_assoc]
    _ = gH j l hjl * gH k t hkt * gX k l hkl * gH k t hkt * gH j l hjl := by
          rw [hg]; simp only [mul_assoc]

/-- (32) `H_[ℓ,t] H_[j,k] X_[k,ℓ] H_[j,k] H_[ℓ,t] ≈ H_[k,ℓ] H_[j,t] X_[k,t] H_[j,t] H_[k,ℓ]`
(`j < k < ℓ < t`; the thesis states it at `1, 2, 3, 4`), by conjugating (31) with
`X_[ℓ,t]`. -/
theorem e32 (hjk : j < k) (hkl : k < l) (hlt : l < t) :
    gH l t hlt * gH j k hjk * gX k l hkl * gH j k hjk * gH l t hlt =
      gH k l hkl * gH j t ((hjk.trans hkl).trans hlt) * gX k t (hkl.trans hlt) *
        gH j t ((hjk.trans hkl).trans hlt) * gH k l hkl := by
  have hjl := hjk.trans hkl
  have hkt := hkl.trans hlt
  have hjt := hjl.trans hlt
  have hcomm : Commute (gω t ^ 4) (gH j k hjk * gX k l hkl * gH j k hjk) := by
    have c1 : Commute (gω t ^ 4) (gH j k hjk) :=
      (c_ωH hjk (hjk.trans hkt).ne' hkt.ne').pow_left 4
    have c2 : Commute (gω t ^ 4) (gX k l hkl) := (c_ωX hkl hkt.ne' hlt.ne').pow_left 4
    exact (c1.mul_right c2).mul_right c1
  have hPY : gH l t hlt * gH j k hjk * gX k l hkl * gH j k hjk * gH l t hlt * gX l t hlt =
      gX l t hlt * (gH l t hlt * gH j k hjk * gX k l hkl * gH j k hjk * gH l t hlt) := by
    calc gH l t hlt * gH j k hjk * gX k l hkl * gH j k hjk * gH l t hlt * gX l t hlt
          = gH l t hlt * (gH j k hjk * gX k l hkl * gH j k hjk) * (gH l t hlt * gX l t hlt) := by
          simp only [mul_assoc]
      _ = gH l t hlt * ((gH j k hjk * gX k l hkl * gH j k hjk) * gω t ^ 4) * gH l t hlt := by
          rw [e18 l t hlt]; simp only [mul_assoc]
      _ = (gH l t hlt * gω t ^ 4) * (gH j k hjk * gX k l hkl * gH j k hjk) * gH l t hlt := by
          rw [← hcomm.eq]; simp only [mul_assoc]
      _ = gX l t hlt * (gH l t hlt * gH j k hjk * gX k l hkl * gH j k hjk * gH l t hlt) := by
          rw [← e23 l t hlt]; simp only [mul_assoc]
  have hYP : gH l t hlt * gH j k hjk * gX k l hkl * gH j k hjk * gH l t hlt =
      gX l t hlt * (gH l t hlt * gH j k hjk * gX k l hkl * gH j k hjk * gH l t hlt) *
        gX l t hlt := by
    rw [← hPY, mul_assoc _ (gX l t hlt), gX_sq, mul_one]
  have h1 : gX l t hlt * gH k t hkt = gH k l hkl * gX l t hlt := (e22 l t k hkl hlt).symm
  have h2 : gX l t hlt * gH j l hjl = gH j t hjt * gX l t hlt :=
    conj_swap' (gX_sq hlt) (e22 l t j hjl hlt)
  have h3 : gX l t hlt * gX k l hkl = gX k t hkt * gX l t hlt := e13 l t k hkl hlt
  have hg : gH j l hjl * gH k t hkt = gH k t hkt * gH j l hjl :=
    e7 j l k t hjl hkt hjk.ne' hkl.ne hjt.ne' hlt.ne'
  have hreord : gH l t hlt * gH j k hjk * gX k l hkl * gH j k hjk * gH l t hlt =
      gH k t hkt * gH j l hjl * gX k l hkl * gH j l hjl * gH k t hkt := by
    rw [e31 j k l t hjk hkl hlt]
    calc gH j l hjl * gH k t hkt * gX k l hkl * gH k t hkt * gH j l hjl
          = gH j l hjl * gH k t hkt * gX k l hkl * (gH k t hkt * gH j l hjl) := by
            simp only [mul_assoc]
      _ = gH k t hkt * gH j l hjl * gX k l hkl * gH j l hjl * gH k t hkt := by
            rw [hg]; simp only [mul_assoc]; rw [hg]
  rw [hYP, hreord]
  exact conj_five (gX_sq hlt) h1 h2 h3 h2 h1

/-- `H_[j,k] ω⁴_[j] ≈ ω⁴_[j] ω⁴_[k] X_[j,k] H_[j,k]` (`j < k`): `H` times `-1` on its
first index is `-X H`, from (23) and (17). -/
theorem eH4 (h : j < k) :
    gH j k h * gω j ^ 4 = gω j ^ 4 * gω k ^ 4 * gX j k h * gH j k h := by
  calc gH j k h * gω j ^ 4 = gH j k h * (gω j ^ 4 * (gω k ^ 4 * gω k ^ 4)) := by
        rw [gω_pow_mul_pow_eq_one k (a := 4) (b := 4) rfl, mul_one]
    _ = gH j k h * (gω j ^ 4 * gω k ^ 4) * gω k ^ 4 := by simp only [mul_assoc]
    _ = gω j ^ 4 * gω k ^ 4 * (gH j k h * gω k ^ 4) := by
        rw [← (c_ω2Hpow h 4).eq]; simp only [mul_assoc]
    _ = gω j ^ 4 * gω k ^ 4 * gX j k h * gH j k h := by rw [← e23]; simp only [mul_assoc]

end Table32

end QCert.Greylyn

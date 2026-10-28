/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.4: Lemma 8.6 for `H` and `CH`, hence Lemma 8.7

The encoding of `H` (resp. `CH`) is a product of letters `H_[a,b]H_[c,d]`
whose four states form the pattern of (36) (resp. (37) for the gate on
wire `0`): by Definition 8.3 each decodes to the multi-controlled `H`
(`dec_hh_one`, `dec_hh_two`, through `Patt`), and they merge by (310) into
the multi-controlled `H` with no control (resp. one), which is the gate.
-/
import QCert.RealCliffordCH.Sec8.E.MergeHg
import QCert.RealCliffordCH.Sec8.E.Patt
import QCert.RealCliffordCH.Sec8.E.Place

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net Eng

theorem xor_ne_xor {s a b : ℕ} (h : a ≠ b) : s ^^^ a ≠ s ^^^ b := by
  intro e; apply h
  have := congrArg (s ^^^ ·) e
  simpa [← Nat.xor_assoc] using this

theorem gInv_inj {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) (h : gInv n x = gInv n y) : x = y := by
  rw [← gray_gInv hx, ← gray_gInv hy, h]

theorem pow_ne_xor {u w : ℕ} (h : u ≠ w) : (2 : ℕ) ^ u ≠ 2 ^ w := by
  intro e; exact h (Nat.pow_right_injective (le_refl 2) e)

theorem two_pow_ne_zero' (u : ℕ) : (2 : ℕ) ^ u ≠ 0 := by positivity

/-- The four states of a pattern are distinct indices. -/
theorem four_distinct {n s u w : ℕ} (huw : u ≠ w) (hs : s < 2 ^ n) (hu : u < n) (hw : w < n) :
    let A := gInv n s
    let B := gInv n (s ^^^ 2 ^ u)
    let C := gInv n (s ^^^ 2 ^ w)
    let D := gInv n (s ^^^ 2 ^ u ^^^ 2 ^ w)
    Distinct4 A B C D ∧ A < 2 ^ n ∧ B < 2 ^ n ∧ C < 2 ^ n ∧ D < 2 ^ n := by
  intro A B C D
  have hu' : 2 ^ u < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hu
  have hw' : 2 ^ w < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hw
  have h1 := Nat.xor_lt_two_pow hs hu'
  have h2 := Nat.xor_lt_two_pow hs hw'
  have h3 := Nat.xor_lt_two_pow h1 hw'
  have ne : ∀ {x y : ℕ}, x < 2 ^ n → y < 2 ^ n → x ≠ y → gInv n x ≠ gInv n y :=
    fun hx hy hxy e => hxy (gInv_inj hx hy e)
  have nb : ∀ {x y : ℕ} (q : ℕ), x.testBit q ≠ y.testBit q → x ≠ y := fun q h e => h (e ▸ rfl)
  have tu : ∀ v, (v ^^^ 2 ^ u).testBit u = !v.testBit u := fun v => testBit_xor_pow_self v u
  have tw : ∀ v, (v ^^^ 2 ^ w).testBit w = !v.testBit w := fun v => testBit_xor_pow_self v w
  have tuw : ∀ v, (v ^^^ 2 ^ w).testBit u = v.testBit u := fun v => testBit_xor_pow_ne huw
  have twu : ∀ v, (v ^^^ 2 ^ u).testBit w = v.testBit w := fun v => testBit_xor_pow_ne (Ne.symm huw)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, gInv_lt hs, gInv_lt h1, gInv_lt h2, gInv_lt h3⟩
  · exact ne hs h1 (nb u (by rw [tu]; cases s.testBit u <;> simp))
  · exact ne hs h2 (nb w (by rw [tw]; cases s.testBit w <;> simp))
  · exact ne hs h3 (nb u (by rw [tuw, tu]; cases s.testBit u <;> simp))
  · exact ne h1 h2 (nb u (by rw [tu, tuw]; cases s.testBit u <;> simp))
  · exact ne h1 h3 (nb w (by rw [tw]; cases (s ^^^ 2 ^ u).testBit w <;> simp))
  · exact ne h2 h3 (nb u (by rw [tuw, tuw, tu]; cases s.testBit u <;> simp))

theorem dec_hh_val {n : ℕ} {A B C D : ℕ} (h : Distinct4 A B C D) (hA : A < 2 ^ n) (hB : B < 2 ^ n)
    (hC : C < 2 ^ n) (hD : D < 2 ^ n) :
    dec n (.hh (ix n A) (ix n B) (ix n C) (ix n D)) = dHH4 n A B C D := by
  have := dec_Hh hA hB hC hD h.1 h.2.2.2.2.2
  rw [if_pos h] at this
  exact this

theorem gx_eq_ix (n s : ℕ) : gx n s = ix n (gInv n s) := rfl

/-- A letter `H_[a,b]H_[c,d]` of the form `x0y0z, x1y0z, x0y1z, x1y1z` (wires
`u > w`) decodes to the multi-controlled `H` with its box on wire `w`. -/
theorem dec_hh_one {k s u w : ℕ} (hwu : w < u) (hun : u < k + 2) (hs : s < 2 ^ (k + 2))
    (hsu : s.testBit u = false) (hsw : s.testBit w = false) :
    dec (k + 2) (.hh (gx (k + 2) s) (gx (k + 2) (s ^^^ 2 ^ u)) (gx (k + 2) (s ^^^ 2 ^ w))
      (gx (k + 2) (s ^^^ 2 ^ u ^^^ 2 ^ w))) = mc (k + 2) .hg [w, u] (ctl2Of s w u) := by
  obtain ⟨hd, hA, hB, hC, hD⟩ := four_distinct (Ne.symm (Nat.ne_of_lt hwu)) hs hun (by omega)
  have hu' : 2 ^ u < 2 ^ (k + 2) := Nat.pow_lt_pow_right (by norm_num) hun
  have hw' : 2 ^ w < 2 ^ (k + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 := Nat.xor_lt_two_pow hs hu'
  have h2 := Nat.xor_lt_two_pow hs hw'
  have h3 := Nat.xor_lt_two_pow h1 hw'
  rw [gx_eq_ix, gx_eq_ix, gx_eq_ix, gx_eq_ix, dec_hh_val hd hA hB hC hD]
  have hp : patt (k + 2) (gInv (k + 2) s) (gInv (k + 2) (s ^^^ 2 ^ u)) (gInv (k + 2) (s ^^^ 2 ^ w))
      (gInv (k + 2) (s ^^^ 2 ^ u ^^^ 2 ^ w)) = some (1, u, w) :=
    patt_one hwu hun hsu hsw (gray_gInv hs) (gray_gInv h1) (gray_gInv h2) (gray_gInv h3)
  simp only [dHH4, hp, if_true, gray_gInv hs]
  rw [← placeAt2_mc k s w u (by omega) hun (by omega)]
  congr 1
  funext j; exact Bool.or_comm _ _

/-- A letter `H_[a,b]H_[c,d]` of the form `x0y0z, x0y1z, x1y0z, x1y1z` (wires
`u > w`) decodes to the multi-controlled `H` with its box on wire `u`. -/
theorem dec_hh_two {k s u w : ℕ} (hwu : w < u) (hun : u < k + 2) (hs : s < 2 ^ (k + 2))
    (hsu : s.testBit u = false) (hsw : s.testBit w = false) :
    dec (k + 2) (.hh (gx (k + 2) s) (gx (k + 2) (s ^^^ 2 ^ w)) (gx (k + 2) (s ^^^ 2 ^ u))
      (gx (k + 2) (s ^^^ 2 ^ u ^^^ 2 ^ w))) = mc (k + 2) .hg [u, w] (ctl2Of s u w) := by
  obtain ⟨hd, hA, hB, hC, hD⟩ := four_distinct (Ne.symm (Nat.ne_of_lt hwu)) hs hun (by omega)
  have hu' : 2 ^ u < 2 ^ (k + 2) := Nat.pow_lt_pow_right (by norm_num) hun
  have hw' : 2 ^ w < 2 ^ (k + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 := Nat.xor_lt_two_pow hs hu'
  have h2 := Nat.xor_lt_two_pow hs hw'
  have h3 := Nat.xor_lt_two_pow h1 hw'
  have hd' : Distinct4 (gInv (k + 2) s) (gInv (k + 2) (s ^^^ 2 ^ w)) (gInv (k + 2) (s ^^^ 2 ^ u))
      (gInv (k + 2) (s ^^^ 2 ^ u ^^^ 2 ^ w)) := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hd
    exact ⟨a2, a1, a3, Ne.symm a4, a6, a5⟩
  rw [gx_eq_ix, gx_eq_ix, gx_eq_ix, gx_eq_ix, dec_hh_val hd' hA hC hB hD]
  have hp : patt (k + 2) (gInv (k + 2) s) (gInv (k + 2) (s ^^^ 2 ^ w)) (gInv (k + 2) (s ^^^ 2 ^ u))
      (gInv (k + 2) (s ^^^ 2 ^ u ^^^ 2 ^ w)) = some (2, u, w) :=
    patt_two hwu hun hsu hsw (gray_gInv hs) (gray_gInv h2) (gray_gInv h1) (gray_gInv h3)
  simp only [dHH4, hp, gray_gInv hs]
  simp only [show ¬ (2 = 1) by omega, if_false]
  exact placeAt2_mc k s u w hun (by omega) (by omega)

end QCert.RealCliffordCH.Sec8.E

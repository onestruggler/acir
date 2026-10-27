/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: the states of the special case of Case 3.2.2.2

In the special case of Case 3.2.2.2 the pivot column has four odd entries
`x₁ < x₂ < x₃ < x₄` of the form `1 + γ³ A` (all `≡ 1 (mod γ³)`), and the
square goes through the states

`C₁ = K†_[x₁,x₂] u`, `C₂ = K†_[x₃,x₄] C₁`, `C₃ = K†_[x₁,x₃] C₂`,
`C₄ = K†_[x₂,x₄] C₃`

(the left column of the diagram in Case 3.2.2.2, and its right column for
the state with `x₂`, `x₃` exchanged).  At each of them at least two of the
four entries are even at the same exponent, so their levels are below that
of `s` (`chain`).
-/
import QCert.BianSelingerUn.MainX

namespace QCert.BianSelingerUn

open Matrix Complex

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

theorem hγ2 : γz ^ 2 = ⟨0, 2⟩ := by decide
theorem hγ3 : γz ^ 3 = ⟨-2, 2⟩ := by decide

/-- `K†_[a,b]` on the entries `a, b` of a numerator, at the same exponent:
the new entries `P, Q` with `γ P = i (x + y)`, `γ Q = i (x - y)`. -/
theorem hasNum_Kd_div {u : St n} {q : Fin n} {k : ℕ} {w : Fin n → GaussianInt}
    (h : HasNum (col u q) k w) {a b : Fin n} (hab : a < b) {P Q : GaussianInt}
    (hP : iz * (w a + w b) = γz * P) (hQ : iz * (w a - w b) = γz * Q) :
    HasNum (col (⟪K a b hab ^ 7⟫ * u) q) k (Function.update (Function.update w a P) b Q) := by
  have h1 := hasNum_Kd h hab.ne
  rw [col_mul, sm_lift, matOf_Kd]
  apply h1.pred
  intro x
  rw [Function.update_apply, Function.update_apply, Function.update_apply,
    Function.update_apply]
  split_ifs <;> first | rfl | exact hQ | exact hP

theorem cols_Kd {u : St n} {p : Fin n} (hu : ∀ q, p < q → col u q = ev q) {a b : Fin n}
    (hab : a < b) (hbp : b ≤ p) : ∀ q, p < q → col (⟪K a b hab ^ 7⟫ * u) q = ev q := by
  intro q hq
  rw [col_mul, sm_lift, matOf_Kd, hu q hq]
  exact twoLevel_mulVec_of_zero hab.ne _ (ev_apply_ne (ne_of_lt ((hab.trans_le hbp).trans hq)))
    (ev_apply_ne (ne_of_lt (lt_of_le_of_lt hbp hq)))

theorem card_lt_of {w w' : Fin n → GaussianInt} {x : Fin n} (hx : GOdd (w x))
    (hx' : ¬ GOdd (w' x)) (hsub : ∀ y, GOdd (w' y) → GOdd (w y)) :
    (oddSet w').card < (oddSet w).card := by
  apply Finset.card_lt_card
  refine ⟨fun y hy => mem_oddSet.2 (hsub y (mem_oddSet.1 hy)), fun hsub' => hx' ?_⟩
  exact mem_oddSet.1 (hsub' (mem_oddSet.2 hx))

theorem GOdd_one_add (A : GaussianInt) : GOdd (1 + γz ^ 3 * A) := by
  rw [hγ3]; unfold GOdd; simp; omega

/-- The level of a state given by a numerator with fewer odd entries. -/
theorem level_lt_of_num {s v : St n} {p : Fin n} (hs : IsPivot s p) {w wv : Fin n → GaussianInt}
    (hw : HasNum (col s p) (lde (col s p)) w) (hv : ∀ q, p < q → col v q = ev q)
    (hwv : HasNum (col v p) (lde (col s p)) wv) (hlt : (oddSet wv).card < (oddSet w).card) :
    level v < level s :=
  level_lt_of_cols hs hv (Or.inr (prof_lt_of hw rfl hwv hlt))

theorem idI1 (A1 A2 : GaussianInt) :
    iz * ((1 + γz ^ 3 * A1) + (1 + γz ^ 3 * A2)) = γz * (γz * (1 + iz * γz * (A1 + A2))) := by
  rw [hγ3]; ext <;> simp [iz, γz] <;> ring

theorem idI2 (A1 A2 : GaussianInt) :
    iz * ((1 + γz ^ 3 * A1) - (1 + γz ^ 3 * A2)) = γz * (γz * (iz * γz * (A1 - A2))) := by
  rw [hγ3]; ext <;> simp [iz, γz] <;> ring

theorem idI5 (A1 A2 A3 A4 : GaussianInt) :
    iz * (γz * (1 + iz * γz * (A1 + A2)) + γz * (1 + iz * γz * (A3 + A4))) =
      γz * (γz * (γz - (A1 + A2 + A3 + A4))) := by
  ext <;> simp [iz, γz] <;> ring

theorem idI6 (A1 A2 A3 A4 : GaussianInt) :
    iz * (γz * (1 + iz * γz * (A1 + A2)) - γz * (1 + iz * γz * (A3 + A4))) =
      γz * (γz * (-(A1 + A2 - A3 - A4))) := by
  ext <;> simp [iz, γz] <;> ring

theorem idI7 (A1 A2 A3 A4 : GaussianInt) :
    iz * (γz * (iz * γz * (A1 - A2)) + γz * (iz * γz * (A3 - A4))) =
      γz * (γz * (-(A1 - A2 + A3 - A4))) := by
  ext <;> simp [iz, γz] <;> ring

theorem idI8 (A1 A2 A3 A4 : GaussianInt) :
    iz * (γz * (iz * γz * (A1 - A2)) - γz * (iz * γz * (A3 - A4))) =
      γz * (γz * (-(A1 - A2 - A3 + A4))) := by
  ext <;> simp [iz, γz] <;> ring

theorem sub_upd {w w' : Fin n → GaussianInt} {x y : Fin n} {P Q : GaussianInt}
    (hP : ¬ GOdd P) (hQ : ¬ GOdd Q) (h : ∀ z, GOdd (w' z) → GOdd (w z)) :
    ∀ z, GOdd (Function.update (Function.update w' x P) y Q z) → GOdd (w z) := by
  intro z hz
  simp only [Function.update_apply] at hz
  split_ifs at hz
  · exact absurd hz hQ
  · exact absurd hz hP
  · exact h z hz

set_option maxHeartbeats 800000 in
/-- The chain of the special case. -/
theorem chain {s u : St n} {p : Fin n} (hs : IsPivot s p) {w : Fin n → GaussianInt}
    (hw : HasNum (col s p) (lde (col s p)) w)
    (hu : ∀ q, p < q → col u q = ev q) {wu : Fin n → GaussianInt}
    (hwu : HasNum (col u p) (lde (col s p)) wu) (hcard : (oddSet wu).card = (oddSet w).card)
    {x1 x2 x3 x4 : Fin n} (h12 : x1 < x2) (h23 : x2 < x3) (h34 : x3 < x4) (h13 : x1 < x3)
    (h24 : x2 < x4) (h4p : x4 ≤ p)
    {A1 A2 A3 A4 : GaussianInt} (e1 : wu x1 = 1 + γz ^ 3 * A1) (e2 : wu x2 = 1 + γz ^ 3 * A2)
    (e3 : wu x3 = 1 + γz ^ 3 * A3) (e4 : wu x4 = 1 + γz ^ 3 * A4) :
    level (⟪K x1 x2 h12 ^ 7⟫ * u) < level s ∧
    level (⟪K x3 x4 h34 ^ 7⟫ * (⟪K x1 x2 h12 ^ 7⟫ * u)) < level s ∧
    level (⟪K x1 x3 h13 ^ 7⟫ * (⟪K x3 x4 h34 ^ 7⟫ * (⟪K x1 x2 h12 ^ 7⟫ * u))) <
      level s ∧
    level (⟪K x2 x4 h24 ^ 7⟫ * (⟪K x1 x3 h13 ^ 7⟫ *
      (⟪K x3 x4 h34 ^ 7⟫ * (⟪K x1 x2 h12 ^ 7⟫ * u)))) < level s := by
  have evn : ∀ c : GaussianInt, ¬ GOdd (γz * c) := not_GOdd_γz_mul
  -- step 1
  have hC1 := hasNum_Kd_div hwu h12 (by rw [e1, e2]; exact idI1 A1 A2)
    (by rw [e1, e2]; exact idI2 A1 A2)
  obtain ⟨w1, hw1⟩ : ∃ w1, w1 = Function.update (Function.update wu x1
      (γz * (1 + iz * γz * (A1 + A2)))) x2 (γz * (iz * γz * (A1 - A2))) := ⟨_, rfl⟩
  rw [← hw1] at hC1
  have w1x3 : w1 x3 = wu x3 := by
    rw [hw1, Function.update_of_ne h23.ne', Function.update_of_ne h13.ne']
  have w1x4 : w1 x4 = wu x4 := by
    rw [hw1, Function.update_of_ne h24.ne', Function.update_of_ne (h13.trans h34).ne']
  -- step 2
  have hC2 := hasNum_Kd_div hC1 h34 (by rw [w1x3, w1x4, e3, e4]; exact idI1 A3 A4)
    (by rw [w1x3, w1x4, e3, e4]; exact idI2 A3 A4)
  obtain ⟨w2, hw2⟩ : ∃ w2, w2 = Function.update (Function.update w1 x3
      (γz * (1 + iz * γz * (A3 + A4)))) x4 (γz * (iz * γz * (A3 - A4))) := ⟨_, rfl⟩
  rw [← hw2] at hC2
  have w2x1 : w2 x1 = γz * (1 + iz * γz * (A1 + A2)) := by
    rw [hw2, Function.update_of_ne (h13.trans h34).ne, Function.update_of_ne h13.ne, hw1,
      Function.update_of_ne h12.ne, Function.update_self]
  have w2x3 : w2 x3 = γz * (1 + iz * γz * (A3 + A4)) := by
    rw [hw2, Function.update_of_ne h34.ne, Function.update_self]
  have w2x2 : w2 x2 = γz * (iz * γz * (A1 - A2)) := by
    rw [hw2, Function.update_of_ne h24.ne, Function.update_of_ne h23.ne, hw1,
      Function.update_self]
  have w2x4 : w2 x4 = γz * (iz * γz * (A3 - A4)) := by rw [hw2, Function.update_self]
  -- step 3
  have hC3 := hasNum_Kd_div hC2 h13 (by rw [w2x1, w2x3]; exact idI5 A1 A2 A3 A4)
    (by rw [w2x1, w2x3]; exact idI6 A1 A2 A3 A4)
  obtain ⟨w3, hw3⟩ : ∃ w3, w3 = Function.update (Function.update w2 x1
      (γz * (γz - (A1 + A2 + A3 + A4)))) x3 (γz * (-(A1 + A2 - A3 - A4))) := ⟨_, rfl⟩
  rw [← hw3] at hC3
  have w3x2 : w3 x2 = γz * (iz * γz * (A1 - A2)) := by
    rw [hw3, Function.update_of_ne h23.ne, Function.update_of_ne h12.ne', w2x2]
  have w3x4 : w3 x4 = γz * (iz * γz * (A3 - A4)) := by
    rw [hw3, Function.update_of_ne h34.ne', Function.update_of_ne (h13.trans h34).ne', w2x4]
  -- step 4
  have hC4 := hasNum_Kd_div hC3 h24 (by rw [w3x2, w3x4]; exact idI7 A1 A2 A3 A4)
    (by rw [w3x2, w3x4]; exact idI8 A1 A2 A3 A4)
  -- the columns beyond `p`
  have c1 := cols_Kd hu h12 (h23.le.trans (h34.le.trans h4p))
  have c2 := cols_Kd c1 h34 h4p
  have c3 := cols_Kd c2 h13 (h34.le.trans h4p)
  have c4 := cols_Kd c3 h24 h4p
  -- the odd entries
  have o1 : GOdd (wu x1) := by rw [e1]; exact GOdd_one_add _
  have sub1 : ∀ z, GOdd (w1 z) → GOdd (wu z) := by
    rw [hw1]; exact sub_upd (evn _) (evn _) (fun _ h => h)
  have sub2 : ∀ z, GOdd (w2 z) → GOdd (wu z) := by
    rw [hw2]; exact sub_upd (evn _) (evn _) sub1
  have sub3 : ∀ z, GOdd (w3 z) → GOdd (wu z) := by
    rw [hw3]; exact sub_upd (evn _) (evn _) sub2
  have sub4 := sub_upd (x := x2) (y := x4) (evn (-(A1 - A2 + A3 - A4)))
    (evn (-(A1 - A2 - A3 + A4)))
    sub3
  have x1w1 : ¬ GOdd (w1 x1) := by
    rw [hw1, Function.update_of_ne h12.ne, Function.update_self]; exact evn _
  have x1w2 : ¬ GOdd (w2 x1) := by rw [w2x1]; exact evn _
  have x1w3 : ¬ GOdd (w3 x1) := by
    rw [hw3, Function.update_of_ne h13.ne, Function.update_self]; exact evn _
  have x1w4 : ¬ GOdd (Function.update (Function.update w3 x2 (γz * (-(A1 - A2 + A3 - A4)))) x4
      (γz * (-(A1 - A2 - A3 + A4))) x1) := by
    rw [Function.update_of_ne (h12.trans h24).ne, Function.update_of_ne h12.ne]
    exact x1w3
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact level_lt_of_num hs hw c1 hC1 (hcard ▸ card_lt_of o1 x1w1 sub1)
  · exact level_lt_of_num hs hw c2 hC2 (hcard ▸ card_lt_of o1 x1w2 sub2)
  · exact level_lt_of_num hs hw c3 hC3 (hcard ▸ card_lt_of o1 x1w3 sub3)
  · exact level_lt_of_num hs hw c4 hC4 (hcard ▸ card_lt_of o1 x1w4 sub4)

end

end QCert.BianSelingerUn

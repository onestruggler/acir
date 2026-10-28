/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Scalar refinement of a source on flat letters (Lemma 50)

The Clifford+CS sources (Bian and Selinger's two-level presentation of
`Uₘ(ℤ[½, i])` and their three-qubit Clifford+CS presentation) have the
powers of `i` as scalars, while CliffCS₂ has those of `ω = e^{iπ/4}`, with
`ω² = i`.  Appendix I refines such a source by a new central generator
`w` with `w² = i`: the refined relations (`RRel`) are the source's, `w`
commuting with every letter, and `w w = gi` for a word `gi` of the source
denoting `i` times the identity.

Lemma 50: the refined presentation is complete as soon as the source is
(`refine_complete`).  Every refined word is `wᵃ` times a source word
(`extract`); two such words with the same matrix, `ωᵃ A = ωᵇ B`, have
`a ≡ b (mod 2)` because the source's matrices have their entries in
`ℚ(i)`, which contains no odd power of `ω` (`parity`: the hypothesis
"no hidden phases" of the lemma, here proved); and then `ω^{b-a}` is a power
of `i`, which the source expresses by `gi`.
-/
import QCert.Minimality.Flat
import QCert.Matrix.Level
import Mathlib.NumberTheory.Real.Irrational

namespace QCert.Minimality

open Matrix

/-! ### Parity in `ℚ(ω)` -/

namespace OmegaParity

/-- An element of `ℚ(i) ⊂ ℚ(ω)`: no odd power of `ω`. -/
abbrev Even (x : QOmega) : Prop := x.a1 = 0 ∧ x.a3 = 0

/-- An element with only odd powers of `ω`. -/
abbrev Odd (x : QOmega) : Prop := x.a0 = 0 ∧ x.a2 = 0

theorem Even.zero : Even 0 := ⟨rfl, rfl⟩

theorem Even.add {x y : QOmega} (hx : Even x) (hy : Even y) : Even (x + y) := by
  obtain ⟨h1, h3⟩ := hx; obtain ⟨k1, k3⟩ := hy
  exact ⟨by simp [h1, k1], by simp [h3, k3]⟩

theorem Even.mul {x y : QOmega} (hx : Even x) (hy : Even y) : Even (x * y) := by
  obtain ⟨h1, h3⟩ := hx; obtain ⟨k1, k3⟩ := hy
  exact ⟨by simp [h1, h3, k1, k3], by simp [h1, h3, k1, k3]⟩

theorem Odd.mul_even {x y : QOmega} (hx : Odd x) (hy : Even y) : Odd (x * y) := by
  obtain ⟨h0, h2⟩ := hx; obtain ⟨k1, k3⟩ := hy
  exact ⟨by simp [h0, h2, k1, k3], by simp [h0, h2, k1, k3]⟩

theorem eq_zero_of_even_odd {x : QOmega} (he : Even x) (ho : Odd x) : x = 0 :=
  Quartic.ext ho.1 he.1 ho.2 he.2

theorem Even.sum {α : Type*} (s : Finset α) (f : α → QOmega) (h : ∀ i ∈ s, Even (f i)) :
    Even (∑ i ∈ s, f i) :=
  Finset.sum_induction f Even (fun _ _ => Even.add) Even.zero h

/-- A matrix with entries in `ℚ(i)`. -/
def MEven {ι κ : Type*} (M : Matrix ι κ QOmega) : Prop := ∀ s t, Even (M s t)

theorem MEven.mul {ι κ ν : Type*} [Fintype κ] {A : Matrix ι κ QOmega} {B : Matrix κ ν QOmega}
    (hA : MEven A) (hB : MEven B) : MEven (A * B) := fun s t => by
  rw [Matrix.mul_apply]; exact Even.sum _ _ fun u _ => (hA s u).mul (hB u t)

theorem MEven.one {ι : Type*} [DecidableEq ι] : MEven (1 : Matrix ι ι QOmega) := fun s t => by
  by_cases h : s = t
  · subst h; rw [Matrix.one_apply_eq]; exact ⟨rfl, rfl⟩
  · rw [Matrix.one_apply_ne h]; exact Even.zero

theorem MEven.lift {Y ι : Type*} [Fintype ι] [DecidableEq ι] (matQ : Y → Matrix ι ι QOmega)
    (h : ∀ y, MEven (matQ y)) (a : FreeMonoid Y) : MEven (FreeMonoid.lift matQ a) := by
  induction a using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact MEven.one
  | mul_of y a ih => rw [map_mul, FreeMonoid.lift_eval_of]; exact (h y).mul ih

theorem MEven.add {ι κ : Type*} {A B : Matrix ι κ QOmega} (hA : MEven A) (hB : MEven B) :
    MEven (A + B) := fun s t => (hA s t).add (hB s t)

theorem MEven.neg {ι κ : Type*} {A : Matrix ι κ QOmega} (hA : MEven A) : MEven (-A) :=
  fun s t => ⟨by simp [(hA s t).1], by simp [(hA s t).2]⟩

theorem MEven.sub {ι κ : Type*} {A B : Matrix ι κ QOmega} (hA : MEven A) (hB : MEven B) :
    MEven (A - B) := by rw [sub_eq_add_neg]; exact hA.add hB.neg

theorem MEven.transpose {ι κ : Type*} {A : Matrix ι κ QOmega} (hA : MEven A) : MEven Aᵀ :=
  fun s t => hA t s

theorem MEven.embed {k m : ℕ} (φ : Fin k → Fin m) : MEven (QCert.embedMat (R := QOmega) φ) := by
  intro s t
  simp only [QCert.embedMat]
  split_ifs
  · exact ⟨rfl, rfl⟩
  · exact Even.zero

/-- A one- or two-level matrix of a matrix over `ℚ(i)` is over `ℚ(i)`. -/
theorem MEven.level {k m : ℕ} (φ : Fin k → Fin m) {M : Matrix (Fin k) (Fin k) QOmega}
    (hM : MEven M) : MEven (QCert.levelMat φ M) := by
  simp only [QCert.levelMat]
  exact MEven.one.add (((MEven.embed φ).mul (hM.sub MEven.one)).mul (MEven.embed φ).transpose)

/-- `ω` in `ℚ(ω)`. -/
abbrev Xq : QOmega := Quartic.X

theorem Xq_pow_eight : Xq ^ 8 = 1 := by decide +kernel

theorem Xq_pow_odd : ∀ r < 8, r % 2 = 1 → Odd (Xq ^ r) := by decide +kernel

theorem Xq_sq : Xq ^ 2 = QOmega.I := by decide +kernel

/-- No hidden phases: `ωᵃ A = ωᵇ B` for nonzero matrices over `ℚ(i)` forces
`a ≡ b (mod 2)`. -/
theorem parity {ι : Type*} {a b : ℕ} {A B : Matrix ι ι QOmega} (hA : MEven A) (hB : MEven B)
    (hB0 : B ≠ 0) (h : Xq ^ a • A = Xq ^ b • B) : a % 2 = b % 2 := by
  obtain ⟨s, t, hst⟩ : ∃ s t, B s t ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hB0 (Matrix.ext hc)
  have hq : Xq ^ a * A s t = Xq ^ b * B s t := by
    have := congrFun (congrFun h s) t
    simpa only [Matrix.smul_apply, smul_eq_mul] using this
  have h2 : Xq ^ ((a + 7 * b) % 8) * A s t = B s t := by
    have e1 : Xq ^ (a + 7 * b) = Xq ^ ((a + 7 * b) % 8) := by
      conv_lhs => rw [← Nat.mod_add_div (a + 7 * b) 8, pow_add, pow_mul, Xq_pow_eight, one_pow,
        mul_one]
    have e2 : Xq ^ (7 * b) * Xq ^ b = 1 := by
      rw [← pow_add, show 7 * b + b = 8 * b by ring, pow_mul, Xq_pow_eight, one_pow]
    calc Xq ^ ((a + 7 * b) % 8) * A s t = Xq ^ (7 * b) * (Xq ^ a * A s t) := by
          rw [← e1, pow_add]; ring
      _ = Xq ^ (7 * b) * (Xq ^ b * B s t) := by rw [hq]
      _ = B s t := by rw [← mul_assoc, e2, one_mul]
  by_contra hne
  have hodd : (a + 7 * b) % 8 % 2 = 1 := by omega
  have ho := (Xq_pow_odd _ (Nat.mod_lt _ (by norm_num)) hodd).mul_even (hA s t)
  rw [h2] at ho
  exact hst (eq_zero_of_even_odd (hB s t) ho)

theorem rat_sqrt2_eq_zero {q r : ℚ} (h : (q : ℝ) + r * Real.sqrt 2 = 0) : q = 0 ∧ r = 0 := by
  have hirr : Irrational (Real.sqrt 2) := by
    have := irrational_sqrt_natCast_iff.mpr (show ¬ IsSquare (2 : ℕ) by decide +kernel)
    simpa using this
  by_cases hr : r = 0
  · subst hr; simp at h; exact ⟨h, rfl⟩
  · exfalso
    apply hirr
    refine ⟨-q / r, ?_⟩
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    push_cast
    field_simp
    linarith

/-- `ℚ(ω)` inside `ℂ`: the reading is injective. -/
theorem toC_injective : Function.Injective QOmega.toC := by
  intro x y hxy
  have hz : QOmega.toC (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [← sub_eq_zero]
  generalize x - y = z at hz
  have h3 : QCert.ω ^ 3 = QCert.ω * Complex.I := by rw [pow_succ, QCert.ω_sq, mul_comm]
  rw [QOmega.toC, Quartic.lift_apply, QCert.ω_sq, h3] at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp [QCert.ω, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.normSq_ofReal] at hre him
  field_simp at hre him
  have h1 := rat_sqrt2_eq_zero (q := 2 * z.a0) (r := z.a1 - z.a3) (by push_cast; linarith)
  have h2 := rat_sqrt2_eq_zero (q := 2 * z.a2) (r := z.a1 + z.a3) (by push_cast; linarith)
  apply Quartic.ext <;> simp <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem mapC_injective {ι κ : Type*} :
    Function.Injective (fun M : Matrix ι κ QOmega => M.map QOmega.toC) :=
  Matrix.map_injective toC_injective

end OmegaParity

open OmegaParity

/-! ### The refined presentation -/

section Refine

variable {Y : Type*} (Γs : WRel Y) (gi : FreeMonoid Y)

/-- The source's words among the refined ones. -/
abbrev ιw : FreeMonoid Y →* FreeMonoid (Option Y) := FreeMonoid.map some

/-- The new scalar `w`. -/
abbrev wl : FreeMonoid (Option Y) := FreeMonoid.of none

/-- The refined relations (Appendix I): the source's, `w` central, and
`w w = gi`. -/
inductive RRel : WRel (Option Y)
  | src {a b : FreeMonoid Y} : Γs a b → RRel (ιw a) (ιw b)
  | comm (y : Y) : RRel (wl * FreeMonoid.of (some y)) (FreeMonoid.of (some y) * wl)
  | sq : RRel (wl * wl) (ιw gi)

variable {Γs gi}

theorem ιw_derivable {a b : FreeMonoid Y} (h : Derivable Γs a b) :
    Derivable (RRel Γs gi) (ιw a) (ιw b) :=
  derivable_map_of (RRel Γs gi) Γs ιw (fun _ _ r => Derivable.of (RRel.src r)) h

theorem wl_comm (u : FreeMonoid (Option Y)) :
    Derivable (RRel Γs gi) (wl * u) (u * wl) := by
  induction u using FreeMonoid.inductionOn' with
  | one => rw [mul_one, one_mul]
  | mul_of x u ih =>
    cases x with
    | none =>
      show Derivable _ (wl * (wl * u)) (wl * u * wl)
      rw [mul_assoc wl u wl]
      exact (Derivable.refl _).mul ih
    | some y =>
      rw [← mul_assoc]
      refine ((Derivable.of (RRel.comm y)).mul (Derivable.refl u)).trans ?_
      rw [mul_assoc, mul_assoc]
      exact (Derivable.refl _).mul ih

theorem wl_pow_comm (a : ℕ) (u : FreeMonoid (Option Y)) :
    Derivable (RRel Γs gi) (wl ^ a * u) (u * wl ^ a) := by
  induction a with
  | zero => rw [pow_zero, one_mul, mul_one]
  | succ a ih =>
    rw [pow_succ, mul_assoc]
    refine ((Derivable.refl _).mul (wl_comm u)).trans ?_
    rw [← mul_assoc, ← mul_assoc]
    exact ih.mul (Derivable.refl _)

/-- Every refined word is a power of `w` times a source word. -/
theorem extract (u : FreeMonoid (Option Y)) :
    ∃ (a : ℕ) (c : FreeMonoid Y), Derivable (RRel Γs gi) u (wl ^ a * ιw c) := by
  induction u using FreeMonoid.inductionOn' with
  | one => exact ⟨0, 1, by rw [pow_zero, map_one, mul_one]⟩
  | mul_of x u ih =>
    obtain ⟨a, c, h⟩ := ih
    cases x with
    | none =>
      refine ⟨a + 1, c, ?_⟩
      refine ((Derivable.refl _).mul h).trans ?_
      rw [← mul_assoc, pow_succ']
    | some y =>
      refine ⟨a, y :: c, ?_⟩
      refine ((Derivable.refl _).mul h).trans ?_
      rw [← mul_assoc]
      refine ((wl_pow_comm a _).symm.mul (Derivable.refl _)).trans ?_
      rw [mul_assoc]
      rfl

/-- The refined letters over `ℚ(ω)`: `w ↦ ω`. -/
def matR {ι : Type*} [DecidableEq ι] [Fintype ι] (matQ : Y → Matrix ι ι QOmega) :
    Option Y → Matrix ι ι QOmega
  | none => Xq • 1
  | some y => matQ y

theorem matR_ιw {ι : Type*} [DecidableEq ι] [Fintype ι] (matQ : Y → Matrix ι ι QOmega)
    (c : FreeMonoid Y) : FreeMonoid.lift (matR matQ) (ιw c) = FreeMonoid.lift matQ c := by
  induction c using FreeMonoid.inductionOn' with
  | one => rw [map_one, map_one, map_one]
  | mul_of y c ih => rw [map_mul, map_mul, map_mul, ih, FreeMonoid.map_of, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of]; rfl

theorem matR_wl_pow {ι : Type*} [DecidableEq ι] [Fintype ι] (matQ : Y → Matrix ι ι QOmega)
    (a : ℕ) : FreeMonoid.lift (matR matQ) (wl ^ a) = Xq ^ a • (1 : Matrix ι ι QOmega) := by
  rw [map_pow, FreeMonoid.lift_eval_of]
  simp only [matR, smul_pow, one_pow]

/-- The refined relations hold for the matrices. -/
theorem refine_sound {ι : Type*} [DecidableEq ι] [Fintype ι] {matQ : Y → Matrix ι ι QOmega}
    (hsound : ∀ a b, Γs a b → FreeMonoid.lift matQ a = FreeMonoid.lift matQ b)
    (hgi : FreeMonoid.lift matQ gi = QOmega.I • 1) {u v : FreeMonoid (Option Y)}
    (h : Derivable (RRel Γs gi) u v) :
    FreeMonoid.lift (matR matQ) u = FreeMonoid.lift (matR matQ) v := by
  refine derivable_sound (fun x y r => ?_) h
  cases r with
  | src r => rw [matR_ιw, matR_ιw, hsound _ _ r]
  | comm y =>
    simp only [map_mul, FreeMonoid.lift_eval_of, matR, smul_mul_assoc, one_mul, mul_smul_comm,
      mul_one]
  | sq =>
    rw [map_mul, FreeMonoid.lift_eval_of, matR_ιw, hgi, ← Xq_sq]
    simp only [matR, smul_mul_smul_comm, one_mul, pow_two]

/-- Lemma 50 for a source on flat letters: the refined presentation is
complete for the matrices as soon as the source is. -/
theorem refine_complete {ι : Type*} [DecidableEq ι] [Fintype ι] {matQ : Y → Matrix ι ι QOmega}
    (hsrc : ∀ a b, FreeMonoid.lift matQ a = FreeMonoid.lift matQ b → Derivable Γs a b)
    (hsound : ∀ a b, Γs a b → FreeMonoid.lift matQ a = FreeMonoid.lift matQ b)
    (hgi : FreeMonoid.lift matQ gi = QOmega.I • 1) (heven : ∀ y, MEven (matQ y))
    (hne : ∀ c, FreeMonoid.lift matQ c ≠ 0) (u v : FreeMonoid (Option Y))
    (h : FreeMonoid.lift (matR matQ) u = FreeMonoid.lift (matR matQ) v) :
    Derivable (RRel Γs gi) u v := by
  obtain ⟨a, c, hu⟩ := extract (Γs := Γs) (gi := gi) u
  obtain ⟨b, c', hv⟩ := extract (Γs := Γs) (gi := gi) v
  have hm : Xq ^ a • FreeMonoid.lift matQ c = Xq ^ b • FreeMonoid.lift matQ c' := by
    have := (refine_sound hsound hgi hu).symm.trans (h.trans (refine_sound hsound hgi hv))
    simpa only [map_mul, matR_wl_pow, matR_ιw, smul_mul_assoc, one_mul] using this
  have hpar := parity (MEven.lift matQ heven c) (MEven.lift matQ heven c') (hne c') hm
  -- the step from the smaller power to the larger
  have step : ∀ {a b : ℕ} {c c' : FreeMonoid Y}, a ≤ b → a % 2 = b % 2 →
      Xq ^ a • FreeMonoid.lift matQ c = Xq ^ b • FreeMonoid.lift matQ c' →
      Derivable (RRel Γs gi) (wl ^ a * ιw c) (wl ^ b * ιw c') := by
    intro a b c c' hab hp hm
    obtain ⟨j, rfl⟩ : ∃ j, b = a + 2 * j := ⟨(b - a) / 2, by omega⟩
    have hX : ∀ k : ℕ, Xq ^ k * Xq ^ (8 * k - k) = 1 := fun k => by
      rw [← pow_add, show k + (8 * k - k) = 8 * k by omega, pow_mul, Xq_pow_eight, one_pow]
    have hc : FreeMonoid.lift matQ c = FreeMonoid.lift matQ (gi ^ j * c') := by
      have := congrArg (fun M => Xq ^ (8 * a - a) • M) hm
      simp only [smul_smul] at this
      rw [mul_comm, hX, one_smul, pow_add, ← mul_assoc, mul_comm (Xq ^ (8 * a - a)), hX,
        one_mul] at this
      rw [this, map_mul, map_pow, hgi, pow_mul, Xq_sq, smul_pow, one_pow, smul_mul_assoc,
        one_mul]
    have hd := ιw_derivable (gi := gi) (hsrc _ _ hc)
    have hpow : ∀ j : ℕ, Derivable (RRel Γs gi) (ιw gi ^ j) (wl ^ (2 * j)) := by
      intro j
      induction j with
      | zero => rw [pow_zero, Nat.mul_zero, pow_zero]
      | succ j ih =>
        rw [pow_succ, Nat.mul_succ, pow_add, pow_two]
        exact ih.mul (Derivable.of RRel.sq).symm
    refine ((Derivable.refl _).mul hd).trans ?_
    rw [map_mul, map_pow, pow_add, mul_assoc]
    exact (Derivable.refl _).mul ((hpow j).mul (Derivable.refl _))
  refine hu.trans (Derivable.trans ?_ hv.symm)
  rcases le_total a b with hab | hab
  · exact step hab hpar hm
  · exact (step hab hpar.symm hm.symm).symm

end Refine

end QCert.Minimality

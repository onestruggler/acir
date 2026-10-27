/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Soundness of the phase-affine rules

Lemma 1 (Figure 1), Lemma 8 (the derived diagonals) and Lemma 9 (Figures 3,
4, 5) of Blake (arXiv:2603.06466): both sides of every rule have the same
pair `(g, q)`, symbolically in the prime `d`.  The rules of `QuadPhase_d`
need `2` invertible (`d` odd) and those of `CubicPhase_d` also `3` (`d > 3`),
as the binomial coordinates do (Lemmas 4 and 5).  Soundness for the matrices
over any ring with a character follows (`theory_sound`), and so does
soundness for the pairs themselves (`pa_sound`), through the faithful
complex matrices.
-/
import QCert.PhaseAffine.Semantics
import QCert.Presentation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

namespace QCert.PhaseAffine

variable {d lv : ℕ}

/-- The pairs `(g, q)` of the gates. -/
local notation "𝒢" => (gateData d lv)

/-! ### Evaluation lemmas -/

theorem PA.low_zero1 (v : Lab d (0 + 1)) : PA.low v = v := rfl
theorem PA.low_zero2 (v : Lab d (0 + 2)) : PA.low v = v := rfl

theorem PA.onBottom_zero1 (p : PA d 1) : (PA.onBottom 0 p : PA d 1) = p := by
  ext v i
  · fin_cases i; simp [PA.onBottom, PA.low_zero1]
  · simp [PA.onBottom, PA.low_zero1]

theorem PA.onBottom_zero2 (p : PA d 2) : (PA.onBottom 0 p : PA d 2) = p := by
  ext v i
  · fin_cases i <;> simp [PA.onBottom, PA.low_zero2]
  · simp [PA.onBottom, PA.low_zero2]

section Data

variable (d lv)

theorem gD_X : (𝒢).gate1 Gate.X = PA.perm fun v => v + 1 := rfl
theorem gD_M (a : (ZMod d)ˣ) : (𝒢).gate1 (Gate.M a) = PA.perm fun v => (a : ZMod d) • v := rfl
theorem gD_Z (h : 1 ≤ lv) : (𝒢).gate1 (Gate.Z h) = PA.diag fun v => v 0 := rfl
theorem gD_S (h : 2 ≤ lv) : (𝒢).gate1 (Gate.S h) = PA.diag fun v => binom2 (v 0) := rfl
theorem gD_T (h : 3 ≤ lv) : (𝒢).gate1 (Gate.T h) = PA.diag fun v => binom3 (v 0) := rfl
theorem gD_CX : (𝒢).gate2 Gate.CX = PA.perm fun v => ![v 0 + v 1, v 1] := rfl
theorem gD_SW : (𝒢).gate2 Gate.SWAP = PA.perm fun v => ![v 1, v 0] := rfl
theorem gD_om (h : 1 ≤ lv) : (𝒢).scalar (Gate.omega h) = 1 := rfl

end Data

theorem gen_g0 {n : ℕ} (g : Gate d lv 0) :
    (𝒢).gen (Gen.gate0 (n := n) g) = PA.scalar ((𝒢).scalar g) := rfl
theorem gen_g1_zero (g : Gate d lv 1) : (𝒢).gen (Gen.gate1 (n := 0) g) = (𝒢).gate1 g :=
  PA.onBottom_zero1 _
theorem gen_g2_zero (g : Gate d lv 2) : (𝒢).gen (Gen.gate2 (n := 0) g) = (𝒢).gate2 g :=
  PA.onBottom_zero2 _
theorem gen_up {n : ℕ} (g : Gen (Gate d lv) n) :
    (𝒢).gen (Gen.up g) = PA.onTop ((𝒢).gen g) := rfl

theorem sem_pad_1_1 (w : C d lv 1) :
    (𝒢).sem 2 (Circuit.pad 1 w) = PA.onBottom 1 ((𝒢).sem 1 w) :=
  GateData.sem_pad _ 1 w
theorem sem_pad_1_2 (w : C d lv 2) :
    (𝒢).sem 3 (Circuit.pad 1 w) = PA.onBottom 1 ((𝒢).sem 2 w) :=
  GateData.sem_pad _ 1 w
theorem sem_pad_2_1 (w : C d lv 1) :
    (𝒢).sem 3 (Circuit.pad 2 w) = PA.onBottom 2 ((𝒢).sem 1 w) :=
  GateData.sem_pad _ 2 w
theorem sem_pad_1_3 (w : C d lv 3) :
    (𝒢).sem 4 (Circuit.pad 1 w) = PA.onBottom 1 ((𝒢).sem 3 w) :=
  GateData.sem_pad _ 1 w

theorem iter_add {n : ℕ} (c : Lab d n) (m : ℕ) :
    (fun v => v + c)^[m] = fun v => v + m • c := by
  induction m with
  | zero => funext v; simp
  | succ m ih => funext v; rw [Function.iterate_succ_apply', ih, succ_nsmul, add_assoc]

theorem iter_cx (m : ℕ) : (fun v : Lab d 2 => ![v 0 + v 1, v 1])^[m] =
    fun v : Lab d 2 => ![v 0 + m * v 1, v 1] := by
  induction m with
  | zero => funext v i; fin_cases i <;> simp
  | succ m ih => funext v i; rw [Function.iterate_succ_apply', ih]; fin_cases i <;> simp; ring

section Powers

variable [NeZero d]

theorem sem_Xf (k : ZMod d) : (𝒢).sem 1 (X ^ᶠ k) = PA.perm fun v i => v i + k := by
  simp only [fpow, map_pow, GateData.sem_of, gen_g1_zero, gD_X, PA.perm_pow, iter_add]
  congr 1; funext v i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, nsmul_eq_mul,
    Pi.natCast_apply, ZMod.natCast_zmod_val]

theorem sem_CXf (k : ZMod d) :
    (𝒢).sem 2 (CX ^ᶠ k) = PA.perm fun v => ![v 0 + k * v 1, v 1] := by
  simp only [fpow, map_pow, GateData.sem_of, gen_g2_zero, gD_CX, PA.perm_pow, iter_cx,
    ZMod.natCast_zmod_val]

theorem diag_fpow {n : ℕ} (q : Lab d n → ZMod d) (k : ZMod d) :
    PA.diag q ^ k.val = PA.diag fun v => k * q v := by
  rw [PA.diag_pow]; congr 1; funext v
  simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem sem_diag_fpow {n : ℕ} (w : C d lv n) (q : Lab d n → ZMod d) (hw : (𝒢).sem n w = PA.diag q)
    (k : ZMod d) : (𝒢).sem n (w ^ᶠ k) = PA.diag fun v => k * q v := by
  rw [fpow, map_pow, hw, diag_fpow]

theorem sem_Zf (h : 1 ≤ lv) (k : ZMod d) : (𝒢).sem 1 (Z h ^ᶠ k) = PA.diag fun v => k * v 0 :=
  sem_diag_fpow _ _ (by simp [gen_g1_zero, gD_Z]) k

theorem sem_Sf (h : 2 ≤ lv) (k : ZMod d) :
    (𝒢).sem 1 (S h ^ᶠ k) = PA.diag fun v => k * binom2 (v 0) :=
  sem_diag_fpow _ _ (by simp [gen_g1_zero, gD_S]) k

theorem sem_Tf (h : 3 ≤ lv) (k : ZMod d) :
    (𝒢).sem 1 (T h ^ᶠ k) = PA.diag fun v => k * binom3 (v 0) :=
  sem_diag_fpow _ _ (by simp [gen_g1_zero, gD_T]) k

end Powers

/-! ### Evaluating both sides -/

/-- Evaluate the pairs of both sides of a rule. -/
macro "pa_simp" : tactic => `(tactic| simp [gen_g0, gen_g1_zero, gen_g2_zero, gen_up, sem_pad_1_1,
  sem_pad_1_2, sem_pad_2_1, sem_pad_1_3, GateData.sem_shift, gD_X, gD_M, gD_Z, gD_S, gD_T, gD_CX,
  gD_SW, gD_om, sem_Xf, sem_CXf, sem_Zf, sem_Sf, sem_Tf, PA.diag_pow, PA.scalar, ZMod.natCast_self])

/-- The same, with the given extra lemmas. -/
macro "pa_simp" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [gen_g0, gen_g1_zero, gen_g2_zero, gen_up, sem_pad_1_1,
  sem_pad_1_2, sem_pad_2_1, sem_pad_1_3, GateData.sem_shift, gD_X, gD_M, gD_Z, gD_S, gD_T, gD_CX,
  gD_SW, gD_om, sem_Xf, sem_CXf, sem_Zf, sem_Sf, sem_Tf, PA.diag_pow, PA.scalar, ZMod.natCast_self,
  $ls,*])

/-- Compare two pairs: every wire of the relabelling, and the phase. -/
macro "pa_eval" : tactic => `(tactic| (
  refine PA.ext (funext fun v => funext fun i => ?_) (funext fun v => ?_)
  · fin_cases i <;>
      simp [PA.perm, PA.diag, PA.scalar, PA.onTop, PA.onBottom, PA.high, PA.low] <;> ring
  · simp [PA.perm, PA.diag, PA.scalar, PA.onTop, PA.onBottom, PA.high, PA.low] <;> ring))

/-- The same, with the binomial coordinates expanded. -/
macro "pa_eval_binom" : tactic => `(tactic| (
  refine PA.ext (funext fun v => funext fun i => ?_) (funext fun v => ?_)
  · fin_cases i <;>
      simp [PA.perm, PA.diag, PA.scalar, PA.onTop, PA.onBottom, PA.high, PA.low] <;> ring
  · simp [PA.perm, PA.diag, PA.scalar, PA.onTop, PA.onBottom, PA.high, PA.low, binom2, binom3]
    field_simp
    ring))

variable [Fact d.Prime]

/-! ### The derived diagonals (Lemma 8) -/

/-- `CZ` has exponent `x y`. -/
theorem sem_CZ (h : 2 ≤ lv) (h2 : (2 : ZMod d) ≠ 0) :
    (𝒢).sem 2 (CZ h) = PA.diag fun v => v 0 * v 1 := by
  pa_simp [CZ]
  pa_eval_binom

/-- `CS` has exponent `x binom y 2`, `x` on the control (wire `1`). -/
theorem sem_CS (h : 3 ≤ lv) (h2 : (2 : ZMod d) ≠ 0) (h3 : (3 : ZMod d) ≠ 0) :
    (𝒢).sem 2 (CS h) = PA.diag fun v => v 1 * binom2 (v 0) := by
  have h6 : (6 : ZMod d) ≠ 0 := by
    rw [show (6 : ZMod d) = 2 * 3 by norm_num]; exact mul_ne_zero h2 h3
  pa_simp [CS, sem_diag_fpow _ _ (sem_CZ (lv := lv) (by omega) h2)]
  pa_eval_binom

/-- `CCZ` has exponent `x y z`. -/
theorem sem_CCZ (h : 3 ≤ lv) (h2 : (2 : ZMod d) ≠ 0) (h3 : (3 : ZMod d) ≠ 0) :
    (𝒢).sem 3 (CCZ h) = PA.diag fun v => v 0 * v 1 * v 2 := by
  have h6 : (6 : ZMod d) ≠ 0 := by
    rw [show (6 : ZMod d) = 2 * 3 by norm_num]; exact mul_ne_zero h2 h3
  pa_simp [CCZ, long]
  pa_eval_binom

/-! ### Every rule is sound (Lemmas 1 and 9) -/

theorem two_ne_zero_of (hd : d ≠ 2) : (2 : ZMod d) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 2 d).1 (by exact_mod_cast h)
  have hp := (Fact.out : d.Prime)
  rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two d this) with h1 | h1
  · exact hp.one_lt.ne' h1
  · exact hd h1

theorem three_ne_zero_of (hd : 3 < d) : (3 : ZMod d) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 3 d).1 (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem six_ne_zero (h2 : (2 : ZMod d) ≠ 0) (h3 : (3 : ZMod d) ≠ 0) : (6 : ZMod d) ≠ 0 := by
  rw [show (6 : ZMod d) = 2 * 3 by norm_num]; exact mul_ne_zero h2 h3

set_option maxHeartbeats 2000000 in
/-- Every rule of the fragment has the same pair `(g, q)` on both sides, given
that `2` is invertible at level `2` and `3` too at level `3`. -/
theorem rules_sound (h2 : 2 ≤ lv → (2 : ZMod d) ≠ 0) (h3 : 3 ≤ lv → (3 : ZMod d) ≠ 0)
    {k : ℕ} {w v : C d lv k} (h : Rules d lv k w v) : (𝒢).sem k w = (𝒢).sem k v := by
  cases h with
  | r1 => pa_simp; pa_eval
  | r2 x y => pa_simp; pa_eval
  | r3 x => pa_simp; pa_eval
  | r4 x => pa_simp; pa_eval
  | r5 x => pa_simp; pa_eval
  | r6 => pa_simp; pa_eval
  | r7 => pa_simp [flip]; pa_eval
  | r8 => pa_simp [long]; pa_eval
  | swap_inv => pa_simp; pa_eval
  | swap_nat1 g => cases g <;> pa_simp <;> pa_eval
  | swap_nat2 g => cases g <;> pa_simp [cyc] <;> pa_eval
  | r19 h => pa_simp; pa_eval
  | r20 h => pa_simp; pa_eval
  | r21 h => pa_simp; pa_eval
  | r22 h x => pa_simp; pa_eval
  | r23 h => pa_simp; pa_eval
  | r24 h => pa_simp; pa_eval
  | r25 h =>
    have h2 := h2 h
    pa_simp; pa_eval_binom
  | r26 h => pa_simp; pa_eval
  | r27 h x =>
    have h2 := h2 h
    pa_simp; pa_eval_binom
  | r28 h =>
    pa_simp [sem_diag_fpow _ _ (sem_CZ h (h2 h)), sem_CZ h (h2 h)]; pa_eval
  | r29 h => pa_simp; pa_eval
  | r30 h =>
    pa_simp [long, sem_CZ h (h2 h)]; pa_eval
  | r31 h => pa_simp; pa_eval
  | r32 h x =>
    have h2 := h2 (by omega)
    have h6 := six_ne_zero h2 (h3 h)
    pa_simp; pa_eval_binom
  | r33 h => pa_simp; pa_eval
  | r34 h =>
    have h2 := h2 (by omega)
    have h6 := six_ne_zero h2 (h3 h)
    pa_simp; pa_eval_binom
  | r35 h a =>
    have h2' := h2 (by omega)
    pa_simp [sem_diag_fpow _ _ (sem_CS h h2' (h3 h)),
      sem_diag_fpow _ _ (sem_CZ (lv := lv) (by omega) h2'), sem_CS h h2' (h3 h)]
    pa_eval_binom
  | r36 h => pa_simp; pa_eval
  | r37 h x =>
    have h2' := h2 (by omega)
    pa_simp [sem_diag_fpow _ _ (sem_CS h h2' (h3 h)), sem_CS h h2' (h3 h)]
    pa_eval
  | r38 h =>
    have h2' := h2 (by omega)
    pa_simp [long, sem_CS h h2' (h3 h), sem_CCZ h h2' (h3 h)]
    pa_eval_binom
  | r39 h => pa_simp; pa_eval
  | r40 h x =>
    have h2' := h2 (by omega)
    pa_simp [sem_diag_fpow _ _ (sem_CCZ h h2' (h3 h)), sem_CCZ h h2' (h3 h)]
    pa_eval
  | r41 h =>
    have h2' := h2 (by omega)
    simp only [long3, seq_cons, seq_nil, one_mul, map_mul]
    rw [sem_pad_1_3, sem_CCZ h h2' (h3 h)]
    simp only [map_mul, map_one, one_mul, GateData.sem_shift, GateData.sem_of, gen_up,
      gen_g2_zero, gD_CX, gD_SW]
    pa_eval
  | r42 h =>
    have h2' := h2 (by omega)
    simp only [long, seq_cons, seq_nil, one_mul, map_mul]
    rw [sem_pad_1_2, sem_CS h h2' (h3 h)]
    simp only [map_mul, map_one, one_mul, GateData.sem_shift, GateData.sem_of, gen_up,
      gen_g2_zero, gD_CX, gD_SW]
    pa_eval

/-! ### Soundness of the theories -/

/-- The hypotheses on `d` at each level: `2` invertible at level `2`, `3`
too at level `3`. -/
structure Admissible (d lv : ℕ) : Prop where
  two : 2 ≤ lv → (2 : ZMod d) ≠ 0
  three : 3 ≤ lv → (3 : ZMod d) ≠ 0

omit [Fact d.Prime] in
theorem admissible_zero : Admissible d 0 := ⟨fun h => by omega, fun h => by omega⟩
omit [Fact d.Prime] in
theorem admissible_one : Admissible d 1 := ⟨fun h => by omega, fun h => by omega⟩
theorem admissible_two (hd : d ≠ 2) : Admissible d 2 :=
  ⟨fun _ => two_ne_zero_of hd, fun h => by omega⟩
theorem admissible_three (hd : 3 < d) : Admissible d 3 :=
  ⟨fun _ => two_ne_zero_of (by omega), fun _ => three_ne_zero_of hd⟩

/-- The theory is sound for the matrices over any ring with a character
(Lemmas 1 and 9). -/
theorem theory_sound (hA : Admissible d lv) {A : Type*} [CommRing A] [StarRing A]
    (ψ : AddChar (ZMod d) A) (hψ : ∀ a, star (ψ a) = ψ (-a)) {n : ℕ} {w v : C d lv n}
    (h : theory d lv n w v) : (sem lv ψ hψ).sem n w = (sem lv ψ hψ).sem n v :=
  GateSem.lift_sound _ (GateSem.padded_sound _ fun k w v hr => Subtype.ext (by
    rw [sem_val, sem_val, rules_sound hA.two hA.three hr])) n w v h

/-- Derivable circuits have the same pair `(g, q)`. -/
theorem pa_sound (hA : Admissible d lv) {n : ℕ} {w v : C d lv n}
    (h : Derivable (theory d lv n) w v) : (𝒢).sem n w = (𝒢).sem n v := by
  have := derivable_sound (sem := (semℂ d lv).gen)
    (fun w v hr => theory_sound hA ZMod.stdAddChar stdAddChar_star hr) h
  have e : ((semℂ d lv).sem n w).1 = ((semℂ d lv).sem n v).1 := congrArg Subtype.val this
  rw [semℂ, sem_val, sem_val] at e
  exact toOp_injective _ ZMod.injective_stdAddChar e

end QCert.PhaseAffine

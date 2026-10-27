/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness for affine circuits (Theorem 1)

Theorem 1 of Blake (arXiv:2603.06466) as in its proof (Lemmas 2, 3): an
affine circuit is its translation column after its linear part
(`affine_collect`); the column is fixed by the image of `0`, so two affine
circuits with the same map have the same column and linear parts with the
same map, which are equal in the theory by the completeness of the linear
fragment (`linear_complete`).

`linear_complete` is the step the paper delegates to Lafont's linear normal
form theorem [17] (with the derivations of Lafont's rules in `Aff_d`,
Lemma 16 and Appendix D.1); it is left as `sorry` here.
-/
import QCert.PhaseAffine.Embed

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

/-! ### Pairs on some of the wires -/

namespace PA

theorem high_eq_tail {n : ℕ} (v : Lab d (n + 1)) : high v = Fin.tail v := by
  funext j; simp only [high, Fin.tail]; congr 1; ext; simp; omega

theorem onTop_f_zero' {n : ℕ} (p : PA d n) (v : Lab d (n + 1)) : (onTop p).f v 0 = v 0 :=
  onTop_f_zero p v 0 rfl

theorem onTop_f_succ {n : ℕ} (p : PA d n) (v : Lab d (n + 1)) (j : Fin n) :
    (onTop p).f v j.succ = p.f (Fin.tail v) j := by
  rw [onTop_f_pos p v j.succ (by simp), high_eq_tail]; congr 1

theorem onTop_q' {n : ℕ} (p : PA d n) (v : Lab d (n + 1)) : (onTop p).q v = p.q (Fin.tail v) := by
  rw [onTop_q, high_eq_tail]

theorem low_one {n : ℕ} (v : Lab d (n + 1)) : (low v : Lab d 1) = fun _ => v 0 := by
  funext i; simp only [low]; congr 1; ext; simp [Fin.fin_one_eq_zero i]

theorem onBottom1_f_zero {n : ℕ} (p : PA d 1) (v : Lab d (n + 1)) :
    (onBottom n p).f v 0 = p.f (fun _ => v 0) 0 := by
  rw [onBottom_f_lt _ _ _ _ (by simp), low_one]; rfl

theorem onBottom1_f_succ {n : ℕ} (p : PA d 1) (v : Lab d (n + 1)) (j : Fin n) :
    (onBottom n p).f v j.succ = v j.succ :=
  onBottom_f_ge _ _ _ _ (by simp)

theorem onBottom1_q {n : ℕ} (p : PA d 1) (v : Lab d (n + 1)) :
    (onBottom n p).q v = p.q (fun _ => v 0) := by
  rw [onBottom_q, low_one]

end PA

local notation "𝒢" => gateData d lv

/-- The translation column `NF_tr(b)` adds `b`. -/
theorem sem_xcol [NeZero d] (n : ℕ) (b : Lab d n) : (𝒢).sem n (xcol n b) = PA.perm (fun v => v + b) := by
  induction n with
  | zero =>
    refine PA.ext (funext fun v => funext fun i => i.elim0) (funext fun v => ?_)
    rfl
  | succ n ih =>
    rw [xcol, map_mul, GateData.sem_shift, ih, fpow, map_pow, GateData.sem_of]
    have hp : ∀ k : ℕ, ((𝒢).gen (Gen.gate1 (n := n) Gate.X)) ^ k =
        PA.onBottom n (PA.perm fun v => v + fun _ => (k : ZMod d)) := by
      intro k
      show (PA.onBottomHom n (PA.perm fun v : Lab d 1 => v + 1)) ^ k = _
      rw [← map_pow, PA.perm_pow, iter_add, PA.onBottomHom_apply]
      congr 2; funext v i; simp
    rw [hp]
    refine PA.ext (funext fun v => funext fun i => ?_) (funext fun v => ?_)
    · simp only [PA.mul_f, Function.comp_apply, PA.perm_f, Pi.add_apply]
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [PA.onTop_f_zero', PA.onBottom1_f_zero]
        simp only [PA.perm_f, Pi.add_apply]
        rw [ZMod.natCast_zmod_val]
      · rw [PA.onTop_f_succ]
        simp only [PA.perm_f, Pi.add_apply]
        rw [show Fin.tail ((PA.onBottom n (PA.perm fun v => v + fun _ => ((b 0).val : ZMod d))).f v)
          j = v j.succ from PA.onBottom1_f_succ _ _ _]
        rfl
    · simp only [PA.mul_q, PA.onTop_q, PA.onBottom_q, PA.perm_q, add_zero]

/-! ### Linear circuits fix `0` and carry no phase -/

theorem gen_lin {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsLin) :
    ((𝒢).gen x).f 0 = 0 ∧ ∀ v, ((𝒢).gen x).q v = 0 := by
  induction x with
  | gate0 c => exact absurd hx (by simp [Gen.IsLin])
  | gate3 g => exact absurd hx (by simp [Gen.IsLin])
  | @gate1 m g =>
    cases g <;> simp only [Gen.IsLin] at hx
    refine ⟨funext fun i => ?_, fun v => rfl⟩
    show (PA.onBottom m _).f 0 i = 0
    by_cases h : (i : ℕ) < 1
    · rw [PA.onBottom_f_lt _ _ _ _ h]; simp [gateData, PA.perm, PA.low]
    · rw [PA.onBottom_f_ge _ _ _ _ h]; rfl
  | @gate2 m g =>
    refine ⟨funext fun i => ?_, fun v => ?_⟩
    · show (PA.onBottom m _).f 0 i = 0
      by_cases h : (i : ℕ) < 2
      · rw [PA.onBottom_f_lt _ _ _ _ h]
        cases g <;> simp [gateData, PA.perm, PA.low] <;> (interval_cases (i : ℕ) <;> simp)
      · rw [PA.onBottom_f_ge _ _ _ _ h]; rfl
    · cases g <;> rfl
  | @up m g ih =>
    obtain ⟨h0, hq⟩ := ih hx
    refine ⟨funext fun i => ?_, fun v => ?_⟩
    · show (PA.onTop _).f 0 i = 0
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [PA.onTop_f_zero']; rfl
      · rw [PA.onTop_f_succ]; exact congrFun h0 j
    · show (PA.onTop _).q v = 0
      rw [PA.onTop_q']; exact hq _

theorem sem_lin {n : ℕ} (w : C d lv n) (hw : IsLinW w) :
    ((𝒢).sem n w).f 0 = 0 ∧ ∀ v, ((𝒢).sem n w).q v = 0 := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨rfl, fun v => rfl⟩
  | mul_of x w ih =>
    have hx : x.IsLin := hw x (by simp)
    have hw' : IsLinW w := fun y hy => hw y (by rw [FreeMonoid.toList_of_mul]; simp [hy])
    obtain ⟨h0, hq⟩ := ih hw'
    obtain ⟨g0, gq⟩ := gen_lin x hx
    rw [map_mul, GateData.sem_of]
    exact ⟨by simp [h0, g0], fun v => by simp [hq, gq]⟩

/-! ### Theorem 1 -/

section Complete

variable [Fact d.Prime]

/-- Completeness of the linear fragment of `Aff_d`: linear circuits
(multipliers, controlled additions, crossings) with the same linear map are
equal in `Aff_d`.  The paper obtains this from Lafont's normal form theorem
for linear circuits [17], cited without proof, whose rules (43)–(51) it
derives in `Aff_d` (Lemma 16); this is that step of the proof of Lemma 3. -/
theorem linear_complete0 {n : ℕ} {w v : C d 0 n} (hw : IsLinW w) (hv : IsLinW v)
    (h : (gateData d 0).sem n w = (gateData d 0).sem n v) : Derivable (theory d 0 n) w v := by
  sorry

/-- Completeness of the linear fragment at every level, from `Aff_d`. -/
theorem linear_complete {n : ℕ} {w v : C d lv n} (hw : IsLinW w) (hv : IsLinW v)
    (h : (𝒢).sem n w = (𝒢).sem n v) : Derivable (theory d lv n) w v := by
  obtain ⟨w0, hw0, rfl⟩ := lin_lift_surj w hw
  obtain ⟨v0, hv0, rfl⟩ := lin_lift_surj v hv
  rw [sem_lift, sem_lift] at h
  exact derivable_lift (linear_complete0 hw0 hv0 h)

/-- Theorem 1 at every level: affine circuits with the same map are equal in
the theory. -/
theorem affine_complete (hA : Admissible d lv) {n : ℕ} {w v : C d lv n} (hw : IsAffW w)
    (hv : IsAffW v) (h : (𝒢).sem n w = (𝒢).sem n v) : Derivable (theory d lv n) w v := by
  obtain ⟨b, hb⟩ := affine_collect w hw
  obtain ⟨c, hc⟩ := affine_collect v hv
  have sw := pa_sound hA (mk_eq_iff.1 hb)
  have sv := pa_sound hA (mk_eq_iff.1 hc)
  rw [map_mul, sem_xcol] at sw sv
  obtain ⟨lw0, -⟩ := sem_lin _ (lin_isLin w hw)
  obtain ⟨lv0, -⟩ := sem_lin _ (lin_isLin v hv)
  have hbc : b = c := by
    have e := congrArg (fun p : PA d n => p.f 0) (sw.symm.trans (h.trans sv))
    simpa [lw0, lv0] using e
  subst hbc
  have hl : (𝒢).sem n (lin w) = (𝒢).sem n (lin v) := by
    have e := sw.symm.trans (h.trans sv)
    have hinv : PA.perm (fun u : Lab d n => u - b) * PA.perm (fun u => u + b) = 1 := by
      refine PA.ext (funext fun u => ?_) (funext fun u => ?_) <;> simp [PA.perm]
    calc (𝒢).sem n (lin w)
        = PA.perm (fun u : Lab d n => u - b) * (PA.perm (fun u => u + b) * (𝒢).sem n (lin w)) := by
          rw [← mul_assoc, hinv, one_mul]
      _ = _ := by rw [e, ← mul_assoc, hinv, one_mul]
  have hlin := mk_eq_iff.2 (linear_complete (lin_isLin w hw) (lin_isLin v hv) hl)
  exact mk_eq_iff.1 (by rw [hb, hc, map_mul, map_mul, hlin])

end Complete

/-- At level `0` every generator is affine. -/
theorem gen_isAff_zero {n : ℕ} (x : Gen (Gate d 0) n) : x.IsAff := by
  induction x with
  | gate0 c => cases c; omega
  | gate1 g => cases g <;> first | omega | trivial
  | gate2 g => trivial
  | gate3 g => nomatch g
  | up g ih => exact ih

/-- At level `0` every circuit is affine. -/
theorem isAffW_zero {n : ℕ} (w : C d 0 n) : IsAffW w := fun x _ => gen_isAff_zero x

end QCert.PhaseAffine

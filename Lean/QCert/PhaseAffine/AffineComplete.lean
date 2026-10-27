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
Lemma 16 and Appendix D.1); it is proved in `Linear` for `Aff_d` and lifted
to every level here.
-/
import QCert.PhaseAffine.Embed
import QCert.PhaseAffine.Linear

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

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

/-! ### Theorem 1 -/

section Complete

variable [Fact d.Prime]

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

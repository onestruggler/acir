/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Boxes commute

A box (`mc` of kind `box`) is diagonal: it multiplies by `-1` the states
whose controls match (`lamOp_box_diag`), so any two boxes commute in the
semantics (`sem_box_comm`), and two boxes idle on a common wire commute in
the theory, by Lemma 5.1 on the other wires (`comm_box_idle`).
-/
import QCert.RealCliffordCH.Sec8.D.N13.Kit

namespace QCert.RealCliffordCH.Sec8.D.N13

open Matrix Circuit Eng SE Net N8 Sim

theorem lamOp_box_diag {N w : ℕ} (c : ℕ → Option Bool) {s t : State 2 N} (hst : s ≠ t) :
    MS.lamOp N [w] c Kind.box.U s t = 0 := by
  unfold MS.lamOp
  by_cases h1 : ∀ j < N, j ∉ [w] → MS.bit s j = MS.bit t j
  · rw [if_pos h1]
    have hw : MS.bit s w ≠ MS.bit t w := by
      intro hw; apply hst; apply MS.state_ext; intro j hj
      by_cases hjw : j = w
      · subst hjw; exact hw
      · exact h1 j hj (by simp [hjw])
    have hrd : (MS.rd [w] s : State 2 1) ≠ MS.rd [w] t := by
      intro e; apply hw; have := congrFun e 0; simpa [MS.rd] using this
    have hU : Kind.box.U = fun u v : State 2 1 => if u = v then (-1 : Q) else 0 := LS.eval_box0
    by_cases hm : MS.Match N [w] c t
    · rw [if_pos hm, hU]; exact if_neg hrd
    · rw [if_neg hm]; exact Matrix.one_apply_ne hrd
  · rw [if_neg h1]

theorem diag_comm {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι Q}
    (hA : ∀ s t, s ≠ t → A s t = 0) (hB : ∀ s t, s ≠ t → B s t = 0) : A * B = B * A := by
  refine Matrix.ext fun s t => ?_
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single s (fun u _ hu => by rw [hA s u (Ne.symm hu), zero_mul]) (by simp),
    Finset.sum_eq_single t (fun u _ hu => by rw [hA u t hu, mul_zero]) (by simp)]
  by_cases hst : s = t
  · subst hst; exact mul_comm _ _
  · rw [hB s t hst, mul_zero, zero_mul]

/-- Two boxes commute in the semantics. -/
theorem sem_box_comm {M t₁ t₂ : ℕ} (c₁ c₂ : ℕ → Option Bool) (h₁ : t₁ < M) (h₂ : t₂ < M) :
    S.sem M (drawn [mc M .box [t₁] c₁, mc M .box [t₂] c₂]) =
      S.sem M (drawn [mc M .box [t₂] c₂, mc M .box [t₁] c₁]) := by
  apply sem_of_eval
  rw [drawn_two, drawn_two, map_mul, map_mul,
    MS.eval_mc c₁ (by simp) (by simpa using h₁) rfl, MS.eval_mc c₂ (by simp) (by simpa using h₂) rfl]
  exact diag_comm (fun _ _ h => lamOp_box_diag c₂ h) (fun _ _ h => lamOp_box_diag c₁ h)

/-- Two boxes idle on a common wire `q` commute (Lemma 5.1 without `q`). -/
theorem comm_box_idle {M q t₁ t₂ : ℕ} (ih : IH (M + 1)) (c₁ c₂ : ℕ → Option Bool) (hq : q ≤ M)
    (h₁ : t₁ ≤ M) (h₂ : t₂ ≤ M) (hq₁ : q ≠ t₁) (hq₂ : q ≠ t₂) (hc₁ : c₁ q = none)
    (hc₂ : c₂ q = none) :
    Comm (M + 1) (mc (M + 1) .box [t₁] c₁) (mc (M + 1) .box [t₂] c₂) := by
  have hA := ToTop.mc (M := M) hq .box [t₁] c₁ rfl (by simp) (by simpa using h₁)
    (by simpa using hq₁) hc₁
  have hB := ToTop.mc (M := M) hq .box [t₂] c₂ rfl (by simp) (by simpa using h₂)
    (by simpa using hq₂) hc₂
  have hd : ∀ t, t ≤ M → q ≠ t → Net.dropW q t < M := fun t ht hqt => by
    simp only [Net.dropW]; split_ifs <;> omega
  refine semIdle ih (ToTop.ofList (.cons hA (.cons hB .nil)))
    (ToTop.ofList (.cons hB (.cons hA .nil))) ?_
  simpa using sem_box_comm (M := M) (c₁ ∘ liftW q) (c₂ ∘ liftW q) (hd t₁ h₁ hq₁) (hd t₂ h₂ hq₂)

end QCert.RealCliffordCH.Sec8.D.N13

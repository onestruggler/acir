/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (354): any colours, any wire, the `XZ`, three wires

From the core (`E354.merge_top_core`): the colours of the controls other than
the merged one by (81) (`P354_flip`, `P354_all`), the `XZ` as the inverse of
the `ZX` by (317) and Lemma B.5 (`P354_xz_top`), any wire by (353) (moving the
merged wire down one swap at a time, `P354_down`).  On three wires the core is
(136), (137).
-/
import QCert.RealCliffordCH.Sec8.D.N15.E354

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

/-- The statement of (354) at a width, a sign, a colouring and a wire. -/
def P354 (N : ℕ) (a : Bool) (x : ℕ → Bool) (w : ℕ) : Prop :=
  ∀ b : Bool, Derivable (theory N)
    (drawn [mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w (some b)),
      mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w (some !b))])
    (mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w none))

theorem setCtl_colOn_congr {N w : ℕ} {x y : ℕ → Bool}
    (h : ∀ i, 1 ≤ i → i < N → i ≠ w → x i = y i) (v : Option Bool) :
    ∀ i < N, setCtl (colOn 1 N x) w v i = setCtl (colOn 1 N y) w v i := by
  intro i hi
  simp only [setCtl, colOn]
  by_cases hiw : i = w
  · rw [if_pos hiw, if_pos hiw]
  · rw [if_neg hiw, if_neg hiw]
    by_cases h1 : 1 ≤ i ∧ i < N
    · rw [if_pos h1, if_pos h1, h i h1.1 h1.2 hiw]
    · rw [if_neg h1, if_neg h1]

theorem P354_congr {N : ℕ} {a : Bool} {x y : ℕ → Bool} {w : ℕ}
    (h : ∀ i, 1 ≤ i → i < N → i ≠ w → x i = y i) (hx : P354 N a x w) : P354 N a y w := by
  intro b
  have e : ∀ v, mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w v) =
      mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N y) w v) :=
    fun v => Net.mc_congr _ _ _ (setCtl_colOn_congr h v)
  have := hx b
  rwa [e, e, e] at this

/-- `x` with the colour of wire `j` exchanged. -/
def flip1 (x : ℕ → Bool) (j : ℕ) : ℕ → Bool := fun i => if i = j then !x i else x i

/-- (81) on a control other than the merged one. -/
theorem P354_flip {N : ℕ} (ih : IH N) {a : Bool} {x : ℕ → Bool} {w j : ℕ} (hj1 : 1 ≤ j)
    (hjN : j < N) (hjw : j ≠ w) (hx : P354 N a x w) : P354 N a (flip1 x j) w := by
  intro b
  have hX := D.xAt_inv N j hjN
  have fl : ∀ v, Derivable (theory N)
      (xAt N j * mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w v) * xAt N j)
      (mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N (flip1 x j)) w v)) := by
    intro v
    have := D.eq81 N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w v) j (x j) hjN
      (by simp; omega) (by simp [setCtl, hjw, colOn, hj1, hjN])
    rw [conj3] at this
    refine this.trans (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_)))
    simp only [setCtl, colOn, flip1]
    by_cases hij : i = j
    · subst hij; simp [hjw, hj1, hjN]
    · rw [if_neg hij]
      simp only [hij, if_false]
  have k := via_conj hX
    (l := [mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w (some b)),
      mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w (some !b))])
    (r := [mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w none)])
    (List.Forall₂.cons (fl _) (List.Forall₂.cons (fl _) List.Forall₂.nil))
    (List.Forall₂.cons (fl _) List.Forall₂.nil) (by rw [drawn_one']; exact hx b)
  rwa [drawn_one'] at k

/-- (354) at every colouring from (354) with every control black. -/
theorem P354_all {N : ℕ} (ih : IH N) {a : Bool} {w : ℕ} (h0 : P354 N a (fun _ => true) w) :
    ∀ x, P354 N a x w := by
  have key : ∀ k, ∀ x : ℕ → Bool, (∀ i, k ≤ i → x i = true) → P354 N a x w := by
    intro k
    induction k with
    | zero => exact fun x hx => P354_congr (fun i _ _ _ => (hx i (Nat.zero_le _)).symm) h0
    | succ k ihk =>
      intro x hx
      by_cases hk : 1 ≤ k ∧ k < N ∧ k ≠ w
      · have hx' : ∀ i, k ≤ i → (fun i => if i = k then true else x i) i = true := by
          intro i hi
          by_cases hik : i = k
          · simp [hik]
          · simp only [if_neg hik]; exact hx i (by omega)
        cases hxk : x k
        · have h1 := P354_flip ih hk.1 hk.2.1 hk.2.2 (ihk _ hx')
          refine P354_congr (fun i _ _ _ => ?_) h1
          simp only [flip1]
          by_cases hik : i = k
          · subst hik; simp [hxk]
          · simp [hik]
        · refine P354_congr (fun i _ _ _ => ?_) (ihk _ hx')
          by_cases hik : i = k
          · subst hik; simp [hxk]
          · simp [hik]
      · have hx' : ∀ i, k ≤ i → (fun i => if i = k then true else x i) i = true := by
          intro i hi
          by_cases hik : i = k
          · simp [hik]
          · simp only [if_neg hik]; exact hx i (by omega)
        refine P354_congr (fun i hi1 hiN hiw => ?_) (ihk _ hx')
        by_cases hik : i = k
        · subst hik; exact absurd ⟨hi1, hiN, hiw⟩ hk
        · simp [hik]
  intro x
  have := key N (fun i => if i < N then x i else true) (fun i hi => by simp; omega)
  exact P354_congr (fun i _ hiN _ => by simp [hiN]) this

/-- (354) moved down one wire by (353). -/
theorem P354_down {N : ℕ} (ih : IH N) {a : Bool} {x : ℕ → Bool} {w : ℕ} (hw1 : 1 ≤ w)
    (hw2 : w + 2 ≤ N) (h : P354 N a x (w + 1)) : P354 N a (x ∘ Net.tau w) w := by
  intro b
  have hsw := mcSwapAll' ih
  have hS := swsw N w hw2
  have mv : ∀ v, Derivable (theory N)
      (swAt N w * mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) (w + 1) v) * swAt N w)
      (mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N (x ∘ Net.tau w)) w v)) := by
    intro v
    have := hsw w hw2 (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) (w + 1) v)
      (by cases a <;> rfl) (by simp) (by simp; omega)
    rw [conj3] at this
    refine this.trans (der_of_eq ?_)
    rw [show ([0] : List ℕ).map (Net.tau w) = [0] by simp [Net.tau]; omega]
    refine Net.mc_congr _ _ _ (fun i hi => ?_)
    simp only [Function.comp, setCtl, colOn, Net.tau]
    split_ifs <;> first | rfl | omega | simp_all | (exfalso; omega)
  have k := via_conj hS
    (l := [mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) (w + 1) (some b)),
      mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) (w + 1) (some !b))])
    (r := [mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) (w + 1) none)])
    (List.Forall₂.cons (mv _) (List.Forall₂.cons (mv _) List.Forall₂.nil))
    (List.Forall₂.cons (mv _) List.Forall₂.nil) (by rw [drawn_one']; exact h b)
  rwa [drawn_one'] at k

/-- (354) at every wire from (354) on the top wire, every colouring. -/
theorem P354_any {N : ℕ} (ih : IH N) {a : Bool} (htop : ∀ x, P354 N a x (N - 1)) :
    ∀ w, 1 ≤ w → w < N → ∀ x, P354 N a x w := by
  have key : ∀ d, ∀ w, 1 ≤ w → w + d + 1 = N → ∀ x, P354 N a x w := by
    intro d
    induction d with
    | zero => intro w _ hw x; rw [show w = N - 1 by omega]; exact htop x
    | succ d ihd =>
      intro w hw1 hw x
      have h := P354_down ih (x := x ∘ Net.tau w) hw1 (by omega) (ihd (w + 1) (by omega) (by omega) _)
      have e : (x ∘ Net.tau w) ∘ Net.tau w = x := by funext i; simp [Function.comp, Net.tau_tau]
      rwa [e] at h
  intro w hw1 hwN x
  exact key (N - 1 - w) w hw1 (by omega) x

end QCert.RealCliffordCH.Sec8.D.N15

/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (307): the box commutes with the swap of two of its controls

At every width from three, by induction on the width (the paper's proof).
The swap of the wires `1, 2` is (275) and that of the wires `2, 3` is (306)
(`IFive`, from five wires on; on four wires (157) and (161) of Appendix D.3,
`W4/A`; on three wires one semantic step).  A swap of the wires `j, j + 1`
with `j ≥ 3` commutes with the factors `W`, `V` of (269) (they act on the
wires `0, 1, 2`) and with its inner box, by `Net.mc_swap_sym` and (307) one
width down (`Net.canonSym_box`).
-/
import QCert.RealCliffordCH.Sec8.D.N8.IFive
import QCert.RealCliffordCH.Sec8.D.W4.A
import QCert.RealCliffordCH.Sec8.D.Small

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

/-- A commutation from a conjugation by an involution. -/
theorem comm_of_conj {N : ℕ} {S A : Circ N} (hS : Derivable (theory N) (S * S) 1)
    (h : Derivable (theory N) (S * A * S) A) : Derivable (theory N) (S * A) (A * S) := by
  have h1 := dright S h
  have e : S * A * S * S = S * A * (S * S) := by simp only [mul_assoc]
  rw [e] at h1
  have h2 := dleft (S * A) hS
  rw [mul_one] at h2
  exact h2.symm.trans h1

/-- `S` commutes with a product when it commutes with each factor. -/
theorem comm_drawn {N : ℕ} (S : Circ N) :
    ∀ (l : List (Circ N)), (∀ x ∈ l, Derivable (theory N) (S * x) (x * S)) →
      Derivable (theory N) (S * drawn l) (drawn l * S)
  | [], _ => by simp [drawn]; exact Derivable.refl _
  | x :: l, h => by
    rw [Net.drawn_cons]
    have h1 := comm_drawn S l (fun y hy => h y (by simp [hy]))
    have h2 := h x (by simp)
    rw [← mul_assoc]
    refine (dright x h1).trans ?_
    rw [mul_assoc, mul_assoc]
    exact dleft _ h2

/-- The box conjugated by a swap: commutation, in the drawn form. -/
theorem comm_drawn2 {N : ℕ} {S A : Circ N} (h : Derivable (theory N) (S * A) (A * S)) :
    Derivable (theory N) (drawn [A, S]) (drawn [S, A]) := by
  simpa [drawn] using h

/-! ## Small widths -/

theorem eq307_3 (ih : IH 3) :
    Derivable (theory 3) (drawn [BxI 3, swAt 3 1]) (drawn [swAt 3 1, BxI 3]) := by
  have hB : BxI 3 = shift (cz : Circ 2) := by
    show mc 3 .box [0] (blackOn 1 3) = _
    rw [show mc 3 .box [0] (blackOn 1 3) = box 2 from mc_canon .box 2]
    rfl
  have hS : swAt 3 1 = shift (swap : Circ 2) := rfl
  rw [hB, hS]
  have e1 : drawn [shift (cz : Circ 2), shift (swap : Circ 2)] = shift ((swap : Circ 2) * cz) := by
    simp [drawn]
  have e2 : drawn [shift (swap : Circ 2), shift (cz : Circ 2)] = shift ((cz : Circ 2) * swap) := by
    simp [drawn]
  rw [e1, e2]
  exact sem_step_shift ih (Fast.sem_of_fast (by decide +kernel))

theorem box3_eq : BxI 4 = r157 := by
  show mc 4 .box [0] (blackOn 1 4) = _
  rw [show mc 4 .box [0] (blackOn 1 4) = box 3 from mc_canon .box 3]
  set_option maxRecDepth 100000 in rfl

theorem eq307_4_1 (ih : IH 4) :
    Derivable (theory 4) (drawn [BxI 4, swAt 4 1]) (drawn [swAt 4 1, BxI 4]) := by
  have h := d157 ih
  have e : l157 = swAt 4 1 * r157 * swAt 4 1 := by
    set_option maxRecDepth 100000 in rfl
  rw [e, ← box3_eq] at h
  exact comm_drawn2 (comm_of_conj (swsw 4 1 (by omega)) h)

theorem eq307_4_2 (ih : IH 4) :
    Derivable (theory 4) (drawn [BxI 4, swAt 4 2]) (drawn [swAt 4 2, BxI 4]) := by
  have h := W4.t161 ih
  have e1 : WE.wcT 4 W4.L161 = swAt 4 2 * BxI 4 * swAt 4 2 := by
    have : mc 4 .box [0] (ctl 4 [(3, true), (2, true), (1, true)] false) = BxI 4 :=
      mc_congr _ _ _ (fun i hi => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl)
    simp only [WE.wcT, W4.L161, List.map, WE.Tk.circ, drawn, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one, this, mul_assoc]
    rfl
  have e2 : WE.wcT 4 W4.R161 = BxI 4 := by
    simp only [WE.wcT, W4.R161, List.map, WE.Tk.circ, drawn, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.prod_cons, List.prod_nil, mul_one]
    exact mc_congr _ _ _ (fun i hi => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl)
  rw [e1, e2] at h
  exact comm_drawn2 (comm_of_conj (swsw 4 2 (by omega)) h)

/-! ## The induction -/

theorem ctl_bx1_tau (n j : ℕ) (hj : 3 ≤ j) (hjN : j + 2 ≤ n + 4) :
    ∀ i < n + 4, (ctlOr (ctlAt 0 true) (blackOn 3 (n + 4)) ∘ Net.tau j) i =
      ctlOr (ctlAt 0 true) (blackOn 3 (n + 4)) i := by
  intro i hi
  have hc : ∀ x, 3 ≤ x → x < n + 4 → ctlOr (ctlAt 0 true) (blackOn 3 (n + 4)) x = some true := by
    intro x h1 h2
    simp [ctlOr, ctlAt, blackOn, h1, h2, show x ≠ 0 by omega]
  simp only [Function.comp_apply, Net.tau]
  split_ifs with h1 h2
  · rw [hc _ (by omega) (by omega), hc _ (by omega) (by omega)]
  · rw [hc _ (by omega) (by omega), hc _ (by omega) (by omega)]
  · rfl

/-- (307) at every width from three. -/
theorem eq307_all : ∀ (N : ℕ), 3 ≤ N → IH N → ∀ (j : ℕ), 1 ≤ j → j + 2 ≤ N →
    Derivable (theory N) (drawn [BxI N, swAt N j]) (drawn [swAt N j, BxI N]) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IHN =>
  intro hN ih j hj hjN
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · obtain rfl : j = 1 := by omega
    exact eq307_3 ih
  · rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
    · exact eq307_4_1 ih
    · exact eq307_4_2 ih
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  rcases (by omega : j = 1 ∨ j = 2 ∨ 3 ≤ j) with rfl | rfl | hj3
  · exact eq307_5_12 m ih 1 (Or.inl rfl)
  · exact eq307_5_12 m ih 2 (Or.inr rfl)
  -- `j ≥ 3`: the factors of (269)
  set S := swAt (m + 5) j
  have hS : Derivable (theory (m + 5)) (S * S) 1 := swsw _ j hjN
  have hSh : HighW 3 S := highW_mono (gLo_swAt (m + 5) j) hj3
  have h269 := eq269_ge4 (m + 1)
  have cW : Derivable (theory (m + 5)) (S * mc (m + 5) .zx [0] (blackOn 1 3))
      (mc (m + 5) .zx [0] (blackOn 1 3) * S) := by
    have e : mc (m + 5) .zx [0] (blackOn 1 3) = Circuit.pad (m + 2) zx2 := zx_bot (m + 2)
    rw [e]
    exact comm_low_high _ _ (lowW_pad _ le_rfl) hSh
  have cV : Derivable (theory (m + 5)) (S * mc (m + 5) .xz [0] (blackOn 1 3))
      (mc (m + 5) .xz [0] (blackOn 1 3) * S) := by
    have e : mc (m + 5) .xz [0] (blackOn 1 3) = Circuit.pad (m + 2) xz2 := xz_bot (m + 2)
    rw [e]
    exact comm_low_high _ _ (lowW_pad _ le_rfl) hSh
  have cC : Derivable (theory (m + 5)) (S * Bx1I (m + 5)) (Bx1I (m + 5) * S) := by
    have hsym : CanonSym .box (ctrlWires (m + 1 + 4) [1]
        (ctlOr (ctlAt 0 true) (blackOn 3 (m + 1 + 4)))).length := by
      rw [ctrl_bx1]
      simp only [List.length_cons, List.length_range']
      exact canonSym_box (m + 3) (fun j' hj' hj'N =>
        IHN (m + 3 + 1) (by omega) (by omega) (ih.mono (by omega)) j' hj' hj'N)
    have h1 := mc_swap_sym (m + 1 + 4) j hjN .box [1]
      (ctlOr (ctlAt 0 true) (blackOn 3 (m + 1 + 4))) rfl (by simp) (by simp) hsym
    have e1 : [1].map (Net.tau j) = [1] := by rw [List.map_singleton, Net.tau_of_lt (by omega)]
    rw [e1, mc_congr _ _ _ (ctl_bx1_tau (m + 1) j hj3 hjN)] at h1
    refine comm_of_conj hS ?_
    simpa [drawn, mul_assoc] using h1
  refine comm_drawn2 ((dleft S h269).trans ((comm_drawn S _ ?_).trans (dright S h269.symm)))
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact cW
  · exact cC
  · exact cV
  · exact cC

end QCert.RealCliffordCH.Sec8.D.N8

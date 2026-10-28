/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (336) with equal colourings

The box on wire `0` (control `c₁` on wire `1`) and the box on wire `1`
(control `c₂` on wire `0`), the wires `2, …` coloured alike, commute.  All
black is `E336a`; the colouring of the wires `2, …` by `Kit.colour_wc`.  `X`
on wire `0` passes the first box (its box wire, (315)) and changes `c₂`; the
swap of the wires `0, 1` exchanges the two boxes, hence `c₁` and `c₂`.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E336a

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-- The two boxes of (336). -/
abbrev bA (N : ℕ) (x : ℕ → Bool) (c : Bool) : Circ N := mc N .box [0] (ctlOr (ctlAt 1 c) (colOn 2 N x))
abbrev bB (N : ℕ) (x : ℕ → Bool) (c : Bool) : Circ N := mc N .box [1] (ctlOr (ctlAt 0 c) (colOn 2 N x))

def A2 : Lt := .g .box [0] [(1, true)] true
def B2 : Lt := .g .box [1] [(0, true)] true

/-- All black controls on wires `0, 1`, the others coloured by `x`. -/
theorem base336 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x : ℕ → Bool) :
    Comm N (bA N x true) (bB N x true) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  have h := r336 m ih
  have e1 : bx0.circ 5 (m + 5) = A2.circ 2 (m + 5) := mc_congr _ _ _ (by ctl_tac)
  have e2 : bxB.circ 5 (m + 5) = B2.circ 2 (m + 5) := mc_congr _ _ _ (by ctl_tac)
  unfold Comm at h
  rw [e1, e2] at h
  have h2 := colour_wc (K := 2) (N := m + 5) (by omega) x (l := [A2, B2]) (r := [B2, A2])
    (by decide) (by decide) h
  have f1 : cX 2 (m + 5) x A2 = bA (m + 5) x true := mc_congr _ _ _ (by ctl_tac)
  have f2 : cX 2 (m + 5) x B2 = bB (m + 5) x true := mc_congr _ _ _ (by ctl_tac)
  have e3 : ∀ y z : Lt, wcX 2 (m + 5) x [y, z] = drawn [cX 2 (m + 5) x y, cX 2 (m + 5) x z] :=
    fun _ _ => rfl
  rw [e3, e3, f1, f2] at h2
  exact h2

/-- (315), as in `N13.lean`: `X` on the box wire commutes with the box. -/
theorem eq315k (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [xAt N 0, Bx N]) (drawn [Bx N, xAt N 0]) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have h := eq308 (k + 1) hN ih 1 le_rfl (by omega) x
  have e : atBot (k + 1) (x : Circ 1) = xAt (k + 1) 0 := (Net.pad_atBot1 k x).symm
  rw [e] at h
  exact h

/-- (315) for the box on wire `0` with coloured controls: `X` on the box wire
passes it. -/
theorem x0_hole (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) (c : Bool) :
    Derivable (theory N) (xAt N 0 * bA N x c * xAt N 0) (bA N x c) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have hc : ∀ i, ((ctlOr (ctlAt 1 c) (colOn 2 (k + 1) x)) i).isSome = true ↔
      kindSp .box ≤ i ∧ i < k + kindSp .box := by
    intro i; simp only [ctlOr, ctlAt, colOn, kindSp]
    by_cases h1 : i = 1
    · subst h1; simp; omega
    · simp only [h1, if_false, Option.none_or]; split_ifs with h <;> simp <;> omega
  have hf := mc_full .box k _ hc
  simp only [kindSp, canonC] at hf
  have e0 : ([0] : List ℕ) = List.range 1 := rfl
  show Derivable _ (xAt (k + 1) 0 * mc (k + 1) .box [0] _ * xAt (k + 1) 0) (mc (k + 1) .box [0] _)
  rw [e0, hf, colourW_eq]
  obtain ⟨hnd, hlt⟩ := whiteWires_ok (k + 1) (List.range 1) (ctlOr (ctlAt 1 c) (colOn 2 (k + 1) x))
  set D := drawn ((whiteWires (k + 1) (List.range 1) (ctlOr (ctlAt 1 c) (colOn 2 (k + 1) x))).map
    (xAt (k + 1)))
  have hD : HighW 1 D := highW_drawn _ (fun a ha => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    rw [MS.mem_whiteWires] at hw
    have h2 := hw.2.2; simp [List.mem_range] at h2
    intro y hy; have := (xAt_wires _ w).2 y hy; omega)
  have hX : LowW 1 (xAt (k + 1) 0) := (xAt_wires (k + 1) 0).1
  have c1 : Derivable (theory (k + 1)) (D * xAt (k + 1) 0) (xAt (k + 1) 0 * D) :=
    comm_low_high _ _ hX hD
  -- `X B ≈ B X` for the canonical box
  have h315 := eq315k (k + 1) hN ih
  have hb := mc_canon .box k
  simp only [kindSp, canonC] at hb
  rw [show Bx (k + 1) = box k from hb] at h315
  rw [drawn_two, drawn_two] at h315
  have e : xAt (k + 1) 0 * (D * box k * D) * xAt (k + 1) 0 =
      (xAt (k + 1) 0 * D) * box k * (D * xAt (k + 1) 0) := by simp only [mul_assoc]
  rw [e]
  refine (dmul (dmul c1.symm (Derivable.refl _)) c1).trans ?_
  have e2 : D * xAt (k + 1) 0 * box k * (xAt (k + 1) 0 * D) =
      D * (xAt (k + 1) 0 * box k) * xAt (k + 1) 0 * D := by simp only [mul_assoc]
  rw [e2]
  refine (dright D (dright _ (dleft D h315.symm))).trans ?_
  have e3 : D * (box k * xAt (k + 1) 0) * xAt (k + 1) 0 * D =
      D * box k * (xAt (k + 1) 0 * xAt (k + 1) 0) * D := by simp only [mul_assoc]
  rw [e3]
  exact cancel_mid (xAt_inv (k + 1) 0 (by omega)) _ _

/-- (81) on the control `0` of the box on wire `1`. -/
theorem flipB0 (N : ℕ) (hN : 3 ≤ N) (x : ℕ → Bool) (c : Bool) :
    Derivable (theory N) (xAt N 0 * bB N x c * xAt N 0) (bB N x (!c)) := by
  have h := eq81 N .box [1] (ctlOr (ctlAt 0 c) (colOn 2 N x)) 0 c (by omega) (by decide)
    (by simp [ctlOr, ctlAt])
  have e : drawn [xAt N 0, bB N x c, xAt N 0] = xAt N 0 * bB N x c * xAt N 0 := by
    simp [drawn, mul_assoc]
  rw [e] at h
  exact h.trans (der_of_eq (mc_congr _ _ _ (by ctl_tac)))

/-- The swap of the wires `0, 1` exchanges the two boxes. -/
theorem swapAB (N : ℕ) (hN : 3 ≤ N) (x : ℕ → Bool) (c : Bool) :
    Derivable (theory N) (swAt N 0 * bA N x c * swAt N 0) (bB N x c) ∧
    Derivable (theory N) (swAt N 0 * bB N x c * swAt N 0) (bA N x c) := by
  have e : ∀ G : Circ N, drawn [swAt N 0, G, swAt N 0] = swAt N 0 * G * swAt N 0 := fun G => by
    simp [drawn, mul_assoc]
  constructor
  · have h := mc_swap N 0 (by omega) .box [0] (ctlOr (ctlAt 1 c) (colOn 2 N x)) rfl (by simp)
      (by simp; omega) (by simp [ctrlWires, ctlOr, ctlAt, colOn])
    rw [e] at h
    refine h.trans (der_of_eq ?_)
    rw [show ([0] : List ℕ).map (Net.tau 0) = [1] from rfl]
    exact mc_congr _ _ _ (fun i hi => by
      simp only [Function.comp, ctlOr, ctlAt, colOn, Net.tau]
      split_ifs <;> first | rfl | omega | simp_all | (exfalso; omega))
  · have h := mc_swap N 0 (by omega) .box [1] (ctlOr (ctlAt 0 c) (colOn 2 N x)) rfl (by simp)
      (by simp; omega) (by simp [ctrlWires, ctlOr, ctlAt, colOn])
    rw [e] at h
    refine h.trans (der_of_eq ?_)
    rw [show ([1] : List ℕ).map (Net.tau 0) = [0] from rfl]
    exact mc_congr _ _ _ (fun i hi => by
      simp only [Function.comp, ctlOr, ctlAt, colOn, Net.tau]
      split_ifs <;> first | rfl | omega | simp_all | (exfalso; omega))

/-- (336) with equal colourings, from five wires on. -/
theorem same336 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x : ℕ → Bool) (c₁ c₂ : Bool) :
    Comm N (bA N x c₁) (bB N x c₂) := by
  have hx := xAt_inv N 0 (by omega)
  have hs := swsw N 0 (by omega)
  have flip2 : ∀ c₁ c₂, Comm N (bA N x c₁) (bB N x c₂) → Comm N (bA N x c₁) (bB N x (!c₂)) :=
    fun c₁ c₂ h => comm_flip h hx (x0_hole N (by omega) ih x c₁) (flipB0 N (by omega) x c₂)
  have sym : ∀ c₁ c₂, Comm N (bA N x c₁) (bB N x c₂) → Comm N (bA N x c₂) (bB N x c₁) :=
    fun c₁ c₂ h => Derivable.symm (Comm.congr (swapAB N (by omega) x c₁).1
      (swapAB N (by omega) x c₂).2 (Comm.conj h hs))
  have tt := base336 N hN ih x
  have tf := flip2 true true tt
  have ft := sym true false tf
  have ff := flip2 false true ft
  cases c₁ <;> cases c₂
  · exact ff
  · exact ft
  · exact tf
  · exact tt

end QCert.RealCliffordCH.Sec8.D.N13

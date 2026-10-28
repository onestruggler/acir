/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (340) from five wires on

The multi-controlled `H` (box wire `0`, `H` on wire `1`) is, by
Definition 2.4, the box on wire `0` with a black control on wire `1`
between two `P ⊗ P` on the wires `0, 1` (`hg_box`; the colours of the
controls above pass `P ⊗ P`), so two of them commute by (335) and (111).
-/
import QCert.RealCliffordCH.Sec8.D.N13.E335

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-- `P ⊗ P` on the wires `0, 1` is an involution (Lemma 5.1, three wires on). -/
theorem pp_inv (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) ((pp : Circ N) * pp) 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 + 2 := ⟨N - 3, by omega⟩
  have h := sem_step_pad (m := m + 1) (k := 2) ih (by omega) (a := (pp : Circ 2) * pp) (b := 1)
    (sem_of_eval (by rw [map_mul, MS.pp_pp, map_one]))
  rwa [map_mul, MS.pad_pp, map_one] at h

theorem lowW_pp (N : ℕ) : LowW 2 ((pp : Circ (N + 2))) := by
  rw [← MS.pad_pp]; exact lowW_pad _ le_rfl

/-- The colouring of the box of the multi-controlled `H`: black on wire `1`. -/
def hgCol (x : ℕ → Bool) : ℕ → Bool := fun j => if j = 1 then true else x j

/-- Definition 2.4: the multi-controlled `H` as a box between two `P ⊗ P`. -/
theorem hg_box (N : ℕ) (hN : 4 ≤ N) (x : ℕ → Bool) :
    Derivable (theory N) (mc N .hg [0, 1] (colOn 2 N x))
      ((pp : Circ N) * mc N .box [0] (colOn 1 N (hgCol x)) * pp) := by
  obtain ⟨j, rfl⟩ : ∃ j, N = j + 2 + 2 := ⟨N - 4, by omega⟩
  have hfull := mc_full .hg (j + 2) (colOn 2 (j + 2 + 2) x) (fun i => by
    simp only [colOn, kindSp]; split_ifs with h <;> simp [h] <;> omega)
  simp only [kindSp] at hfull
  rw [show ([0, 1] : List ℕ) = List.range 2 from rfl, hfull]
  obtain ⟨W, hWd⟩ : ∃ W, W = whiteWires (j + 2 + 2) (List.range 2) (colOn 2 (j + 2 + 2) x) :=
    ⟨_, rfl⟩
  rw [← hWd]
  obtain ⟨hnd, hlt⟩ := whiteWires_ok (j + 2 + 2) (List.range 2) (colOn 2 (j + 2 + 2) x)
  rw [← hWd] at hnd hlt
  have hW : ∀ w ∈ W, 2 ≤ w := fun w hw => by
    rw [hWd, MS.mem_whiteWires] at hw
    have := hw.2.2; simp [List.mem_range] at this; omega
  have e1 : canonC .hg (j + 2) = (pp : Circ (j + 2 + 2)) * box (j + 3) * pp := by
    show drawn [pp, box (j + 3), pp] = _; simp [drawn, mul_assoc]
  rw [e1, colourW_eq]
  have hD : HighW 2 (drawn (W.map (xAt (j + 2 + 2)))) := highW_drawn _ (fun a ha => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    intro y hy; have := (xAt_wires _ w).2 y hy; have := hW w hw; omega)
  have hc := comm_low_high _ _ (lowW_pp (j + 2)) hD
  have step : ∀ B : Circ (j + 2 + 2), Derivable (theory (j + 2 + 2))
      (drawn (W.map (xAt (j + 2 + 2))) * (pp * B * pp) * drawn (W.map (xAt (j + 2 + 2))))
      (pp * (drawn (W.map (xAt (j + 2 + 2))) * B * drawn (W.map (xAt (j + 2 + 2)))) * pp) := by
    intro B
    have e : drawn (W.map (xAt (j + 2 + 2))) * (pp * B * pp) * drawn (W.map (xAt (j + 2 + 2))) =
        (drawn (W.map (xAt (j + 2 + 2))) * pp) * B * (pp * drawn (W.map (xAt (j + 2 + 2)))) := by
      simp only [mul_assoc]
    rw [e]
    refine (dmul (dmul hc (Derivable.refl _)) hc.symm).trans ?_
    simp only [mul_assoc]; exact Derivable.refl _
  refine (step _).trans (dmul (dmul (Derivable.refl _) ?_) (Derivable.refl _))
  have hb := mc_canon .box (j + 3)
  simp only [kindSp, canonC] at hb
  rw [← hb]
  have h := mc_colour (j + 2 + 2) .box [0] (blackOn 1 (j + 3 + 1)) W hnd (fun w hw => by
    refine ⟨hlt w hw, by simp; have := hW w hw; omega, ?_⟩
    simp only [blackOn]; rw [if_pos ⟨by have := hW w hw; omega, hlt w hw⟩])
  rw [colourW_eq] at h
  refine h.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
  simp only [blackOn, colOn, hgCol, hWd, MS.mem_whiteWires]
  by_cases h1 : i = 1
  · subst h1; simp
  · by_cases h0 : i = 0
    · subst h0; simp
    · simp only [h1, if_false, show 1 ≤ i ∧ i < j + 2 + 2 from ⟨by omega, hi⟩,
        show 2 ≤ i ∧ i < j + 2 + 2 from ⟨by omega, hi⟩, if_true]
      cases hx : x i <;> simp [hi, hx, List.mem_range] <;> omega

/-- (340) from five wires on. -/
theorem comm340_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .hg [0, 1] (colOn 2 N x)) (mc N .hg [0, 1] (colOn 2 N y)) :=
  Comm.congr (hg_box N (by omega) x).symm (hg_box N (by omega) y).symm
    (Comm.conj (comm335_ge5 N hN ih (hgCol x) (hgCol y)) (pp_inv N (by omega) ih))

end QCert.RealCliffordCH.Sec8.D.N13

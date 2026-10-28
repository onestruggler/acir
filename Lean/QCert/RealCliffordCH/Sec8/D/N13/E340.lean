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
theorem pp_inv (m : ℕ) (ih : IH (m + 1 + 2)) :
    Derivable (theory (m + 1 + 2)) ((pp : Circ (m + 1 + 2)) * pp) 1 := by
  have h := sem_step_pad (m := m + 1) (k := 2) ih (by omega) (a := (pp : Circ 2) * pp) (b := 1)
    (sem_of_eval (by rw [map_mul, MS.pp_pp, map_one]))
  rwa [map_mul, MS.pad_pp, map_one] at h

theorem lowW_pp (n : ℕ) : LowW 2 ((pp : Circ (n + 2))) := by
  rw [← MS.pad_pp]; exact lowW_pad _ le_rfl

/-- The colouring of the box of the multi-controlled `H`: black on wire `1`. -/
def hgCol (x : ℕ → Bool) : ℕ → Bool := fun j => if j = 1 then true else x j

/-- The box with `j + 3` controls, on `j + 2 + 2` wires. -/
def bxj (j : ℕ) : Circ (j + 2 + 2) := box (j + 3)

theorem mch_eq (j : ℕ) :
    canonC .hg (j + 2) = (pp : Circ (j + 2 + 2)) * (bxj j * pp) := by
  show drawn [pp, box (j + 3), pp] = _
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one]
  rfl

/-- Definition 2.4: the multi-controlled `H` as a box between two `P ⊗ P`. -/
theorem hg_box (j : ℕ) (x : ℕ → Bool) :
    Derivable (theory (j + 2 + 2)) (mc (j + 2 + 2) .hg [0, 1] (colOn 2 (j + 2 + 2) x))
      ((pp : Circ (j + 2 + 2)) * (mc (j + 2 + 2) .box [0] (colOn 1 (j + 2 + 2) (hgCol x)) * pp)) := by
  have hfull := mc_full .hg (j + 2) (colOn 2 (j + 2 + 2) x) (fun i => by
    simp only [colOn, kindSp]; split_ifs with h <;> simp [h] <;> omega)
  simp only [kindSp] at hfull
  rw [show ([0, 1] : List ℕ) = List.range 2 from rfl, hfull, mch_eq]
  obtain ⟨W, hWd⟩ : ∃ W, W = whiteWires (j + 2 + 2) (List.range 2) (colOn 2 (j + 2 + 2) x) :=
    ⟨_, rfl⟩
  rw [← hWd]
  obtain ⟨hnd, hlt⟩ := whiteWires_ok (j + 2 + 2) (List.range 2) (colOn 2 (j + 2 + 2) x)
  rw [← hWd] at hnd hlt
  have hW : ∀ w ∈ W, 2 ≤ w := fun w hw => by
    rw [hWd, MS.mem_whiteWires] at hw
    have := hw.2.2; simp [List.mem_range] at this; omega
  rw [colourW_eq]
  set D := drawn (W.map (xAt (j + 2 + 2))) with hDdef
  have hD : HighW 2 D := highW_drawn _ (fun a ha => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    intro y hy; have := (xAt_wires _ w).2 y hy; have := hW w hw; omega)
  have hc : Derivable (theory (j + 2 + 2)) ((pp : Circ (j + 2 + 2)) * D) (D * pp) :=
    (comm_low_high _ _ (lowW_pp (j + 2)) hD).symm
  have e : D * ((pp : Circ (j + 2 + 2)) * (bxj j * pp)) * D =
      (D * pp) * bxj j * (pp * D) := by simp only [mul_assoc]
  refine (der_of_eq e).trans ?_
  refine (dmul (dmul hc.symm (Derivable.refl _)) hc).trans ?_
  have e2 : (pp : Circ (j + 2 + 2)) * D * bxj j * (D * pp) =
      pp * ((D * bxj j * D) * pp) := by simp only [mul_assoc]
  refine (der_of_eq e2).trans ?_
  refine dleft _ (dright _ ?_)
  have hb : mc (j + 2 + 2) .box [0] (blackOn 1 (j + 3 + 1)) = bxj j := mc_canon .box (j + 3)
  refine (der_of_eq (congrArg (fun t => D * t * D) hb.symm)).trans ?_
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
    Comm N (mc N .hg [0, 1] (colOn 2 N x)) (mc N .hg [0, 1] (colOn 2 N y)) := by
  obtain ⟨j, rfl⟩ : ∃ j, N = j + 2 + 2 := ⟨N - 4, by omega⟩
  have hpp : Derivable (theory (j + 2 + 2)) ((pp : Circ (j + 2 + 2)) * pp) 1 :=
    pp_inv (j + 1) ih
  have h := Comm.conj (comm335_ge5 (j + 2 + 2) hN ih (hgCol x) (hgCol y)) hpp
    (u := (pp : Circ (j + 2 + 2))) (v := pp)
  refine Comm.congr ((hg_box j x).trans ?_).symm ((hg_box j y).trans ?_).symm h <;>
    simp only [mul_assoc] <;> exact Derivable.refl _

end QCert.RealCliffordCH.Sec8.D.N13

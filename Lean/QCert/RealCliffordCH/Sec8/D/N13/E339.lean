/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (339) from six wires on

See `E339a` for the frame and the tools; the decided steps are in `E339r1`
(two rotations), `E339r2` (the runs) and `E339r3` (their five-wire steps).

Status: not built.  Its decided steps need too much memory as written (one
declaration of four runs in `E337r1` passed 4.7 GB; `E322`, imported through
`E322x`, needs about 11 GB): see `HANDOVER.md` before building.  Nothing
imports it.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E339r1
import QCert.RealCliffordCH.Sec8.D.N13.E339r2
import QCert.RealCliffordCH.Sec8.D.N13.E339r3

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

theorem commRR339 (m : ℕ) (ih : IH (m + 6)) {b1 b3 c3 : Bool} {r r' : Lt}
    (hr : r ∈ rots b1 true b3) (hr' : r' ∈ rots false c3 true) :
    Comm (m + 6) (r.circ 4 (m + 6))
      (wc 4 (m + 6) mL * r'.circ 4 (m + 6) * wc 4 (m + 6) mL') := by
  obtain ⟨r0, hr0, e0⟩ := rots_base (m + 1) ih hr
  obtain ⟨r1, hr1, e1⟩ := rots_base (m + 1) ih hr'
  have h := check_sound (m := m + 1) (frame 4) ih (allD_nil 5 (m + 1))
    (chkRR339 b1 b3 c3 r0 hr0 r1 hr1)
  simp only [wc_append, wc_one', wc5_mL, wc5_mL', rots_rebase (rots2_sub hr0),
    rots_rebase (rots2_sub hr1)] at h
  have hb : Comm (m + 6) (r0.circ 4 (m + 6))
      (wc 4 (m + 6) mL * r1.circ 4 (m + 6) * wc 4 (m + 6) mL') := by
    unfold Comm
    rw [drawn_two, drawn_two]
    simpa only [mul_assoc] using h
  have hMM := MM_inv m ih
  exact comm_basesC hMM.1 hMM.2 hb (base_circ e0) (base_circ e1)

theorem commBR339 (m : ℕ) (ih : IH (m + 6)) (x : ℕ → Bool) (c₁ c₂ c3 : Bool) {r : Lt}
    (hr : r ∈ rots false c3 true) :
    Comm (m + 6) (boxN (m + 6) (xE c₁ c₂ x) c₂ true)
      (wc 4 (m + 6) mL * r.circ 4 (m + 6) * wc 4 (m + 6) mL') := by
  obtain ⟨r0, hr0, e0⟩ := rots_base (m + 1) ih hr
  have h := gcl m ih x c₂ (x 4) (RW r0) (chkBR339 c₂ (x 4) c3 r0 hr0)
    (chkTBR c₂ (x 4) c3 r0 hr0) (RW_loc c3 r0 hr0)
  have eG : cX 5 (m + 6) x (G4 c₂ (x 4)) = boxN (m + 6) (xE c₁ c₂ x) c₂ true := by
    show mc _ _ _ _ = _
    refine mc_congr _ _ _ (fun i hi => ?_)
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ 5 ≤ i) with
      rfl | rfl | rfl | rfl | rfl | h5
    all_goals (simp only [ctlX, ctlOr, ctlAt, colOn, xE]; split_ifs <;>
      first | rfl | (exfalso; omega) | simp_all | omega)
  simp only [RW, wc_append, wc_one', wc5_mL, wc5_mL', rots_rebase (rots2_sub hr0), eG] at h
  have hb : Comm (m + 6) (boxN (m + 6) (xE c₁ c₂ x) c₂ true)
      (wc 4 (m + 6) mL * r0.circ 4 (m + 6) * wc 4 (m + 6) mL') := by
    unfold Comm
    rw [drawn_two, drawn_two]
    simpa only [mul_assoc] using h
  have hMM := MM_inv m ih
  exact comm_basesC (A0 := boxN (m + 6) (xE c₁ c₂ x) c₂ true) hMM.1 hMM.2 hb (Or.inl rfl)
    (base_circ e0)

/-! ## The pairs and the core -/

theorem pairs339 (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ c₃ : Bool) :
    ∀ a ∈ (pcs4 c₂ true c₁).map (cX 4 (m + 6) (xE c₁ c₂ x)),
      ∀ b ∈ ((pcs4 false c₃ true).map (cX 4 (m + 6) (yS c₃ y))).map
        (fun a => wc 4 (m + 6) mL * a * wc 4 (m + 6) mL'), Comm (m + 6) a b := by
  intro a ha b hb
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hb'
  rcases pcs4_cls hg with hr | rfl <;> rcases pcs4_cls hg' with hr' | rfl
  · rw [rots_cX hr, rots_cX hr']
    exact commRR339 m ih hr hr'
  · rw [rots_cX hr, P3'_cX]
    exact Comm.congr (Derivable.refl _) (remB m ih c₃ y).symm
      (commRBs (m + 1) ih c₂ c₁ c₃ y hr)
  · rw [P3'_cX, rots_cX hr']
    exact commBR339 m ih x c₁ c₂ c₃ hr'
  · rw [P3'_cX, P3'_cX]
    exact Comm.congr (Derivable.refl _) (remB m ih c₃ y).symm
      (commBBs (m + 1) ih c₂ c₃ (xE c₁ c₂ x) y)

/-- (339) in the frame: the box on wire `0` black on wire `2`, the
multi-controlled `H` on the wires `1, 3` white on wire `2`. -/
theorem comm339E (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ c₃ : Bool) :
    Comm (m + 6) (mc (m + 6) .box [0] (colOn 1 (m + 6) (xE c₁ c₂ x))) (BE (m + 6) c₃ y) := by
  have ex : Derivable (theory (m + 6)) (mc (m + 6) .box [0] (colOn 1 (m + 6) (xE c₁ c₂ x)))
      (wcX 4 (m + 6) (xE c₁ c₂ x) (pcs4 c₂ true c₁)) := expX (m + 6) (by omega) ih (xE c₁ c₂ x)
  have eS : Derivable (theory (m + 6)) (mc (m + 6) .box [0] (colOn 1 (m + 6) (yS c₃ y)))
      (wcX 4 (m + 6) (yS c₃ y) (pcs4 false c₃ true)) := expX (m + 6) (by omega) ih (yS c₃ y)
  have hMM := MM_inv m ih
  have eB : Derivable (theory (m + 6)) (BE (m + 6) c₃ y)
      (drawn (((pcs4 false c₃ true).map (cX 4 (m + 6) (yS c₃ y))).map
        (fun a => wc 4 (m + 6) mL * a * wc 4 (m + 6) mL'))) :=
    (expBE m ih c₃ y).trans ((dright _ (dleft _ eS)).trans (conj_drawn hMM.1 hMM.2 _))
  exact Comm.congr ex.symm eB.symm (comm_drawn _ _ (pairs339 m ih x y c₁ c₂ c₃))

/-! ## Back to the interface -/

/-- The controls of the box of (339). -/
abbrev cA339 (N : ℕ) (x : ℕ → Bool) (c₁ c₂ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 N x))
/-- The controls of the multi-controlled `H` of (339). -/
abbrev cB339 (N : ℕ) (y : ℕ → Bool) (c₃ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 0 c₃) (colOn 3 N y)

/-- (339) when the colourings are black, resp. white, on wire `3`. -/
theorem comm339_core (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ c₃ : Bool)
    (hx : x 3 = true) (hy : y 3 = false) :
    Comm (m + 6) (mc (m + 6) .box [0] (cA339 (m + 6) x c₁ c₂))
      (mc (m + 6) .hg [1, 2] (cB339 (m + 6) y c₃)) := by
  have hA := swBH ih 2 (by omega) .box (Or.inl rfl) [0] [0] (colOn 1 (m + 6) (xE c₁ c₂ x))
    (cA339 (m + 6) x c₁ c₂) rfl (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [cA339, colOn, ctlOr, ctlAt, xE, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))
  have hB := swBH ih 2 (by omega) .hg (Or.inr rfl) [1, 3] [1, 2]
    (ctlOr (ctlAt 0 c₃) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y))) (cB339 (m + 6) y c₃) rfl
    (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [cB339, colOn, ctlOr, ctlAt, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))
  exact comm_flip (comm339E m ih x y c₁ c₂ c₃) (swsw (m + 6) 2 (by omega)) hA hB

/-- (339) from six wires on. -/
theorem comm339_ge6 (N : ℕ) (hN : 6 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ c₃ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 N x))))
      (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₃) (colOn 3 N y))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 6 := ⟨N - 6, by omega⟩
  refine sep_reduce (P := fun x y => Comm (m + 6) (mc (m + 6) .box [0] (cA339 (m + 6) x c₁ c₂))
    (mc (m + 6) .hg [1, 2] (cB339 (m + 6) y c₃))) ?_ ?_
    (fun x y hx hy => comm339_core m ih x y c₁ c₂ c₃ hx hy) x y hxy
  · intro x y j hj hjN h
    have rA := swBH ih j hjN .box (Or.inl rfl) [0] [0] (cA339 (m + 6) (x ∘ Net.tau j) c₁ c₂)
      (cA339 (m + 6) x c₁ c₂) rfl (by decide) (by intro t ht; simp at ht; omega)
      (by simp only [List.map_cons, List.map_nil, Net.tau]; split_ifs <;> first | rfl | omega)
      (fun i hi => by
        simp only [cA339, ctlOr, ctlAt_tau (show 2 < j by omega), ctlAt_tau (show 1 < j by omega),
          colOn_tau (show 3 ≤ j by omega) hjN x hi])
    have rB := swBH ih j hjN .hg (Or.inr rfl) [1, 2] [1, 2] (cB339 (m + 6) (y ∘ Net.tau j) c₃)
      (cB339 (m + 6) y c₃) rfl (by decide) (by intro t ht; simp at ht; omega)
      (by simp only [List.map_cons, List.map_nil, Net.tau]; split_ifs <;> first | rfl | omega)
      (fun i hi => by
        simp only [cB339, ctlOr, ctlAt_tau (show 0 < j by omega),
          colOn_tau (show 3 ≤ j by omega) hjN y hi])
    exact Comm.congr rA rB (Comm.conj h (swsw _ j hjN))
  · intro x y h
    have hx := xAt_inv (m + 6) 3 (by omega)
    refine comm_flip h hx ?_ ?_
    · have e := eq81 (m + 6) .box [0] (cA339 (m + 6) (flipAt 3 x) c₁ c₂) 3 (flipAt 3 x 3)
        (by omega) (by decide) (by simp [cA339, ctlOr, ctlAt, colOn])
      rw [show drawn [xAt (m + 6) 3, mc (m + 6) .box [0] (cA339 (m + 6) (flipAt 3 x) c₁ c₂),
          xAt (m + 6) 3] = xAt (m + 6) 3 * mc (m + 6) .box [0] (cA339 (m + 6) (flipAt 3 x) c₁ c₂) *
          xAt (m + 6) 3 by simp [drawn, mul_assoc]] at e
      refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
      have := colOn_flip (lo := 3) (N := m + 6) (by omega) x i
      simp only [cA339, setCtl, ctlOr, ctlAt] at this ⊢
      split_ifs at this ⊢ <;> simp_all
    · have e := eq81 (m + 6) .hg [1, 2] (cB339 (m + 6) (flipAt 3 y) c₃) 3 (flipAt 3 y 3)
        (by omega) (by decide) (by simp [cB339, ctlOr, ctlAt, colOn])
      rw [show drawn [xAt (m + 6) 3, mc (m + 6) .hg [1, 2] (cB339 (m + 6) (flipAt 3 y) c₃),
          xAt (m + 6) 3] = xAt (m + 6) 3 * mc (m + 6) .hg [1, 2] (cB339 (m + 6) (flipAt 3 y) c₃) *
          xAt (m + 6) 3 by simp [drawn, mul_assoc]] at e
      refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
      have := colOn_flip (lo := 3) (N := m + 6) (by omega) y i
      simp only [cB339, setCtl, ctlOr, ctlAt] at this ⊢
      split_ifs at this ⊢ <;> simp_all

end QCert.RealCliffordCH.Sec8.D.N13

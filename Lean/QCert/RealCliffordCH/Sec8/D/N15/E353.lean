/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (353): the multi-controlled `ZX` commutes with the swap of two controls

The canonical `ZX` with all its controls is, by Definition 2.4,
`CH · B' · CH · B'` with `B'` the box on wire `1` (`zx (k + 1)`), so the swap
of the wires `j, j + 1`, `j ≥ 2`, passes it: the `CH` and the swap of the
wires `0, 1` are on the wires below, and the box passes it by (307)
(`comm_zx_sw_ge2`).  On three wires the swap of the wires `1, 2` is (127)
(`comm_zx_sw_3`).  From four wires on, the swap of the wires `1, 2` (the
paper's third case, by another route): by (333) and (353) for the wires `2, 3`
the gate is `H' B H' B` with `H'` the multi-controlled `H` on wire `0` with its
box on wire `3` (black on `1, 2, 4, …`) and `B` the box on wire `1` (black on
`0, 2, 3, …`); `B` is the product of its versions idle and white on wire `2`
((309)), and the white one passes `H'` ((339)) and is an involution ((311)), so
the gate is `H' Bᵢ H' Bᵢ` with `Bᵢ` idle on wire `2`; the swap of the wires `1,
2` fixes `H'` ((313)) and moves the box wire of `Bᵢ` to wire `2`, which is `Bᵢ`
again by (274) (`comm_zx_sw_1`).  The `XZ` is the inverse of the `ZX` ((317)).
-/
import QCert.RealCliffordCH.Sec8.D.N15.Base
import QCert.RealCliffordCH.Sec8.D.Small

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

/-! ## The canonical gates -/

theorem mc_zx_canon (k : ℕ) : mc (k + 1) .zx [0] (blackOn 1 (k + 1)) = zx k :=
  mc_canon .zx k

theorem mc_box_canon (k : ℕ) : mc (k + 1) .box [0] (blackOn 1 (k + 1)) = box k :=
  mc_canon .box k

theorem lowW_ch (k : ℕ) : LowW 2 (ch : Circ (k + 2)) := by
  rw [← MS.pad_ch k]; exact lowW_pad _ le_rfl

theorem lowW_swap (k : ℕ) : LowW 2 (swap : Circ (k + 2)) := by
  rw [← MS.pad_swap k]; exact lowW_pad _ le_rfl

theorem highW_swAt {N j : ℕ} (hj : 2 ≤ j) : HighW 2 (swAt N j) :=
  fun g hg => le_trans hj ((swAt_wires N j).2 g hg)

/-! ## The swap of two controls above wire `1` -/

/-- (353) for the `ZX` and the swap of the wires `j, j + 1`, `j ≥ 2`. -/
theorem comm_zx_sw_ge2 (k : ℕ) (ih : IH (k + 1 + 1)) (j : ℕ) (hj : 2 ≤ j)
    (hjN : j + 2 ≤ k + 1 + 1) :
    D.Comm (k + 1 + 1) (mc (k + 1 + 1) .zx [0] (blackOn 1 (k + 1 + 1))) (swAt (k + 1 + 1) j) := by
  have hbox : D.Comm (k + 1 + 1) (box (k + 1)) (swAt (k + 1 + 1) j) := by
    have h := D.eq307 (k + 1 + 1) (by omega) ih j (by omega) hjN
    unfold D.Bx at h
    rw [mc_box_canon] at h
    exact h
  have hlow : ∀ g : Circ (k + 1 + 1), LowW 2 g → D.Comm (k + 1 + 1) g (swAt (k + 1 + 1) j) :=
    fun g hg => by unfold D.Comm; rw [drawn_two', drawn_two']; exact comm_low_high g _ hg (highW_swAt hj)
  have hB : D.Comm (k + 1 + 1) (conj swap (box (k + 1))) (swAt (k + 1 + 1) j) := by
    have := N13.comm_drawn [swap, box (k + 1), swap] [swAt (k + 1 + 1) j] (fun a ha b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha hb
      subst hb
      rcases ha with rfl | rfl | rfl
      · exact hlow _ (lowW_swap k)
      · exact hbox
      · exact hlow _ (lowW_swap k))
    rwa [drawn_one'] at this
  rw [mc_zx_canon]
  have := N13.comm_drawn [ch, conj swap (box (k + 1)), ch, conj swap (box (k + 1))]
    [swAt (k + 1 + 1) j] (fun a ha b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha hb
      subst hb
      rcases ha with rfl | rfl | rfl | rfl
      · exact hlow _ (lowW_ch k)
      · exact hB
      · exact hlow _ (lowW_ch k)
      · exact hB)
  rwa [drawn_one'] at this

/-! ## Three wires: (127) -/

theorem comm_zx_sw_3 (ih : IH 3) :
    D.Comm 3 (mc 3 .zx [0] (blackOn 1 3)) (swAt 3 1) := by
  rw [show mc 3 .zx [0] (blackOn 1 3) = zx 2 from mc_zx_canon 2]
  have h := d127 ih
  unfold D.Comm
  simp only [l127, r127, circW, List.map, L.circ] at h
  convert h using 1 <;> simp [drawn, zx, box, conj, place2, MS.pad_ch, MS.pad_swap, mul_assoc]

end QCert.RealCliffordCH.Sec8.D.N15

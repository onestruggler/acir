/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rule (39)

`D((-1)_[0](-1)_[1])` is the box on wire `0` with white controls (the Gray
codes `G(0) = 0…00` and `G(1) = 0…01` differ on wire `0`), and
`D(H_[0,1]H_[3,2])` the gadget, the multi-controlled `H` with its box on
wire `1`, its `H` on wire `0` and white controls; they commute by (338).
-/
import QCert.RealCliffordCH.Sec8.E.Rule24

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

theorem isOnes_zero : IsOnes 0 0 := ⟨fun j hj => absurd hj (by omega), by decide⟩

theorem tOf_zero {n : ℕ} (hn : 1 ≤ n) : tOf n 0 = 0 :=
  tOf_eq isOnes_zero (by
    calc 0 + 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)

/-- `D((-1)_[0](-1)_[1])`: the box on wire `0`, every other control white. -/
theorem dec_zz01 {M : ℕ} :
    dec (M + 3) (Zz (M + 3) 0 1) = mc (M + 3) .box [0] (colOn 1 (M + 3) fun _ => false) := by
  have h8 : 1 < 2 ^ (M + 3) := Nat.one_lt_two_pow (by omega)
  rw [dec_Zz (by omega) h8, show (1 : ℕ) = 0 + 1 from rfl, dZZ_succ, dZZ1_mc (M + 2),
    tOf_zero (by omega)]
  refine Net.mc_congr _ _ _ (fun j hj => ?_)
  rcases j with _ | j
  · simp [ctlOf, colOn]
  · simp [ctlOf, colOn, bitOf, gray, show j + 1 < M + 3 by omega]

/-- The gadget, white controls written with `colOn`. -/
theorem gadget_colOn {M : ℕ} :
    gadget (M + 3) = mc (M + 3) .hg [1, 0] (colOn 2 (M + 3) fun _ => false) := by
  rw [show M + 3 = (M + 1) + 2 from rfl, gadget_mc]
  refine Net.mc_congr _ _ _ (fun j hj => ?_)
  rcases j with _ | _ | j
  · simp [ctl2Of, colOn]
  · simp [ctl2Of, colOn]
  · simp [ctl2Of, colOn, bitOf, show j + 2 < M + 1 + 2 by omega]

/-- (39) decodes to (338). -/
theorem dec39 {M : ℕ} (ih : IH (M + 3)) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf [Zz (M + 3) 0 1, Hh (M + 3) 0 1 3 2]))
      (decW (M + 3) (wordOf [Hh (M + 3) 0 1 3 2, Zz (M + 3) 0 1])) := by
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_0132 (by omega : 3 ≤ M + 3), dec_zz01, gadget_colOn]
  have h := D.eq338 (M + 3) (by omega) ih (fun _ => false) (fun _ => false) false
  have e : mc (M + 3) .box [0] (ctlOr (ctlAt 1 false) (colOn 2 (M + 3) fun _ => false)) =
      mc (M + 3) .box [0] (colOn 1 (M + 3) fun _ => false) := by
    refine Net.mc_congr _ _ _ (fun j hj => ?_)
    simp only [ctlOr, ctlAt, colOn]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [e] at h
  unfold D.Comm at h
  rw [drawn_two, drawn_two] at h
  exact h.symm

end QCert.RealCliffordCH.Sec8.E

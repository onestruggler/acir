/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Table entries for the engine: Equation (81) on letters

`x81E`: a multi-controlled letter conjugated by `X = H Z H` on one of its
local control wires is the letter with that control's colour exchanged
(`Colour.eq81'`).  `qE`: `H` or `Z` on a local wire passes a letter that
avoids it (`Anchors.qcommE` on five local wires).
-/
import QCert.RealCliffordCH.Sec8.D.Colour
import QCert.RealCliffordCH.Sec8.D.N8.Anchors

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE

/-- `X` on the local wire `j`, as three letters. -/
def xL (j : ℕ) : List Lt := [.s (.H j), .s (.Z j), .s (.H j)]

/-- (81) as a table entry: `X` on a local control wire around a letter
exchanges the colour of that control. -/
theorem x81E (m K j : ℕ) (hj : j < K) (Kd : Kind) (tg : List ℕ) (cs cs' : List (ℕ × Bool))
    (b v : Bool) (hjt : j ∉ tg) (hc : cs.lookup j = some v)
    (hcs : ∀ i < K, cs'.lookup i = if i = j then some (!v) else cs.lookup i) :
    Derivable (theory (m + K)) (wc K (m + K) (xL j ++ [.g Kd tg cs b] ++ xL j))
      (wc K (m + K) [.g Kd tg cs' b]) := by
  have e1 : wc K (m + K) (xL j ++ [.g Kd tg cs b] ++ xL j) =
      drawn [xAt (m + K) j, mc (m + K) Kd tg (ctl K cs b), xAt (m + K) j] := by
    rw [D.xAt_eq]
    simp [wc, xL, drawn, circW, Lt.circ, mul_assoc]
  rw [e1]
  have hcj : ctl K cs b j = some v := by simp [ctl, hj, hc]
  refine (D.eq81' (m + K) Kd tg (ctl K cs b) j v (by omega) hjt hcj).trans (Net.der_of_eq ?_)
  have e2 : (Lt.g Kd tg cs' b).circ K (m + K) = mc (m + K) Kd tg (ctl K cs' b) := rfl
  rw [show wc K (m + K) [.g Kd tg cs' b] = (Lt.g Kd tg cs' b).circ K (m + K) by
    simp [wc, drawn], e2]
  refine Net.mc_congr _ _ _ (fun i hi => ?_)
  simp only [setCtl, ctl]
  by_cases hij : i = j
  · subst hij; simp [hj, hcs i hj]
  · rw [if_neg hij]
    by_cases hik : i < K
    · rw [if_pos hik, if_pos hik, hcs i hik, if_neg hij]
    · rw [if_neg hik, if_neg hik]

/-- `H` or `Z` on a local wire `q` passes a letter avoiding it (five local
wires). -/
theorem qE (m q : ℕ) (hq : q ≤ 4) (x : Lt) (hx : x.ok 5 = true) (hav : x.avoids q = true)
    (l : L) (hl : l = .H q ∨ l = .Z q) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [x, .s l]) (wc 5 (m + 5) [.s l, x]) :=
  qcommE m 4 q hq x hx hav l hl

end QCert.RealCliffordCH.Sec8.D.N8

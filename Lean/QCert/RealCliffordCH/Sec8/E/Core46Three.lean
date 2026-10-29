/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5, rule (46): the core on three wires

On three wires the decoded letters of (46) are the gates of (147) (`D.eq147`,
Appendix D.2): their box wire is idle, and a multi-controlled `H` with one
control placed on `b :: ps` is the controlled `H` placed on `ps`
(`placeG_shift_cons`).
-/
import QCert.RealCliffordCH.Sec8.E.Rule46
import QCert.RealCliffordCH.Sec8.D.Small

namespace QCert.RealCliffordCH.Sec8.E.C46

open Circuit Net Eng

theorem K1_eq : (L.K 1).circ 3 = (shift ch : Circ 3) := by
  show shift (place2 2 0 ch) = shift ch
  congr 1

theorem K0_eq : (L.K 0).circ 3 = atBot 3 (ch : Circ 2) := by
  show place2 3 0 ch = _
  exact pad_atBot2 1 ch

theorem C1_eq : (L.C 1).circ 3 = (shift cz : Circ 3) := by
  show shift (place2 2 0 cz) = shift cz
  congr 1

/-- `H` on wire `0` with its box on wire `2`: the controlled `H` on the wires `0, 1`. -/
theorem hg20_three :
    Derivable (theory 3) (placeG 3 (shift (ch : Circ 2)) [2, 0, 1]) ((L.K 0).circ 3) := by
  have h := placeG_shift_cons (n := 3) (ch : Circ 2) (p := 2) (ps := [0, 1]) (by decide)
    (by intro q hq; simp at hq; omega) rfl
  rw [placeG_pair 3 _ (by omega)] at h
  rw [K0_eq]; exact h

theorem pl021 : placeG 3 (shift (ch : Circ 2)) [0, 2, 1] = swAt 3 1 * (shift ch * swAt 3 1) := by
  have h : netK [0, 2, 1] [0, 2, 1].length = [1] := by decide
  simp only [placeG, netL_eq, h, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.singleton_append, drawn, atBot_self, List.prod_cons,
    List.prod_nil, mul_one, mul_assoc]

theorem pl102 : placeG 3 (shift (ch : Circ 2)) [1, 0, 2] = swAt 3 0 * (shift ch * swAt 3 0) := by
  have h : netK [1, 0, 2] [1, 0, 2].length = [0] := by decide
  simp only [placeG, netL_eq, h, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.singleton_append, drawn, atBot_self, List.prod_cons,
    List.prod_nil, mul_one, mul_assoc]

theorem eA3 :
    Derivable (theory 3) (A46 0) (circW 3 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1]) := by
  have e : A46 0 = colourW 3 [1] (placeG 3 (shift (ch : Circ 2)) [2, 0, 1]) := rfl
  have e1 : colourW 3 [1] (placeG 3 (shift (ch : Circ 2)) [2, 0, 1]) =
      xAt 3 1 * placeG 3 (shift (ch : Circ 2)) [2, 0, 1] * xAt 3 1 := by
    simp [colourW, drawn, mul_assoc]
  have e2 : circW 3 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] =
      xAt 3 1 * (L.K 0).circ 3 * xAt 3 1 := by
    simp [circW, drawn, xAt_eq, mul_assoc]
  rw [e, e1, e2]
  exact dright _ (dleft _ hg20_three)

theorem eD3 : Derivable (theory 3) (D46 0) (circW 3 [L.K 0]) := by
  have e : D46 0 = colourW 3 [] (placeG 3 (shift (ch : Circ 2)) [2, 0, 1]) := rfl
  have e1 : colourW 3 [] (placeG 3 (shift (ch : Circ 2)) [2, 0, 1]) =
      placeG 3 (shift (ch : Circ 2)) [2, 0, 1] := by simp [colourW, drawn]
  rw [e, e1, show circW 3 [L.K 0] = (L.K 0).circ 3 by simp [circW, drawn]]
  exact hg20_three

theorem eB3 : B46 0 = circW 3 [L.H 2, L.Z 2, L.H 2, L.K 1, L.H 2, L.Z 2, L.H 2] := by
  have e : B46 0 = colourW 3 [2] (placeG 3 (shift (ch : Circ 2)) (List.range 3)) := rfl
  rw [e, placeG_id, ← K1_eq]
  simp [colourW, circW, drawn, xAt_eq, mul_assoc]

theorem eC3 : C46 0 = circW 3 [L.S 1, L.K 1, L.S 1] := by
  have e : C46 0 = colourW 3 [] (placeG 3 (shift (ch : Circ 2)) [0, 2, 1]) := rfl
  rw [e, pl021, ← K1_eq]
  simp [colourW, circW, drawn, swAt_eq, mul_assoc]

theorem eF3 : F46 0 = circW 3 [L.S 0, L.K 1, L.S 0] := by
  have e : F46 0 = colourW 3 [] (placeG 3 (shift (ch : Circ 2)) [1, 0, 2]) := rfl
  rw [e, pl102, ← K1_eq]
  simp [colourW, circW, drawn, swAt_eq, mul_assoc]

theorem eZ3 : Z46 0 = circW 3 [L.H 2, L.Z 2, L.H 2, L.C 1, L.H 2, L.Z 2, L.H 2] := by
  have e : Z46 0 = colourW 3 [2] (placeG 3 (shift (cz : Circ 2)) (List.range 3)) := rfl
  rw [e, placeG_id, ← C1_eq]
  simp [colourW, circW, drawn, xAt_eq, mul_assoc]

/-- The core of (46) on three wires is (147). -/
theorem core46_three (ih : IH 3) : Core46 0 := by
  have h := D.eq147 0 ih
  rw [D.N8.pad_zero3, D.N8.pad_zero3] at h
  have eL : D.l147 = circW 3 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] *
      circW 3 [L.H 2, L.Z 2, L.H 2, L.K 1, L.H 2, L.Z 2, L.H 2] * circW 3 [L.S 1, L.K 1, L.S 1] *
      circW 3 [L.K 0] * circW 3 [L.S 0, L.K 1, L.S 0] *
      circW 3 [L.H 2, L.Z 2, L.H 2, L.C 1, L.H 2, L.Z 2, L.H 2] * circW 3 [L.S 1, L.K 1, L.S 1] *
      circW 3 [L.H 2, L.Z 2, L.H 2, L.K 1, L.H 2, L.Z 2, L.H 2] := by
    simp only [D.l147, circW, drawn, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.singleton_append, List.prod_cons, List.prod_nil,
      List.prod_append, mul_one, mul_assoc]
  have eR : D.r147 = circW 3 [L.H 2, L.Z 2, L.H 2, L.K 1, L.H 2, L.Z 2, L.H 2] *
      circW 3 [L.S 1, L.K 1, L.S 1] *
      circW 3 [L.H 2, L.Z 2, L.H 2, L.C 1, L.H 2, L.Z 2, L.H 2] *
      circW 3 [L.S 0, L.K 1, L.S 0] * circW 3 [L.K 0] * circW 3 [L.S 1, L.K 1, L.S 1] *
      circW 3 [L.H 2, L.Z 2, L.H 2, L.K 1, L.H 2, L.Z 2, L.H 2] *
      circW 3 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] := by
    simp only [D.r147, circW, drawn, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.singleton_append, List.prod_cons, List.prod_nil,
      List.prod_append, mul_one, mul_assoc]
  rw [eL, eR] at h
  unfold Core46
  rw [eB3, eC3, eF3, eZ3]
  -- replace the two letters `A`, `Dd` (equal up to a derivation)
  refine (dmul (dmul (dmul (dmul (dmul (dmul (dmul eA3 (Derivable.refl _)) (Derivable.refl _))
    eD3) (Derivable.refl _)) (Derivable.refl _)) (Derivable.refl _)) (Derivable.refl _)).trans
    (h.trans ?_)
  exact dmul (dmul (dmul (dmul (Derivable.refl _) eD3.symm) (Derivable.refl _)) (Derivable.refl _))
    eA3.symm

end QCert.RealCliffordCH.Sec8.E.C46

/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (310), (312), (313): the multi-controlled `H`

With at least two controls the multi-controlled `H` on the wires `0, 1` is
`P ⊗ P`, the box with one more control on wire `1`, `P ⊗ P` (`HgPP.hgPP`),
so its statements follow from those of the box (the paper's proofs):

* (310) from (309) (`eq310_of`, from five wires on, where the merged gate
  still has two controls);
* (312) from (311) and `(P ⊗ P)² = 1` (`eq312_of`, from four wires on);
* (313) from (307), the swap of two controls acting on the wires `2, …`
  where it commutes with `P ⊗ P` (`eq313_of`, from four wires on).
-/
import QCert.RealCliffordCH.Sec8.D.N8.I309
import QCert.RealCliffordCH.Sec8.D.N8.HgPP

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

/-- `(P ⊗ P)² = 1` on the wires `0, 1`. -/
theorem pp_sq (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (ppAt N 0 1 * ppAt N 0 1) 1 := by
  have h2 : Derivable (theory 2) ((pp : Circ 2) * pp) 1 :=
    ih 2 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))
  have h := der_atBot h2 N (by omega)
  rw [atBot_mul, show atBot N (1 : Circ 2) = 1 from by
    have := atBot_mul N (1 : Circ 2) 1; rw [mul_one] at this; exact (mul_eq_left.1 this.symm)] at h
  rwa [ppAt, placeG_pair N _ (by omega)]

theorem hg_ctrl_len (N : ℕ) (hN : 2 ≤ N) (c : ℕ → Option Bool)
    (hc : ∀ j, 2 ≤ j → j < N → (c j).isSome = true) :
    (ctrlWires N [0, 1] c).length = N - 2 := by
  have e : ctrlWires N [0, 1] c = List.range' 2 (N - 2) := by
    unfold ctrlWires
    rw [range_two N hN, List.filter_cons, List.filter_cons]
    simp only [List.contains_cons, List.contains_nil, beq_self_eq_true, Bool.true_or, Bool.not_true,
      Bool.and_false, Bool.false_eq_true, if_false, show ((1 : ℕ) == 0) = false by rfl,
      Bool.false_or, Bool.or_false]
    refine List.filter_eq_self.2 (fun j hj => ?_)
    rw [List.mem_range'_1] at hj
    have h0 : (j == 0) = false := by simp; omega
    have h1 : (j == 1) = false := by simp; omega
    simp [hc j (by omega) (by omega), h0, h1]
  rw [e, List.length_range']

/-- `hgPP` for the colourings of the interface. -/
theorem hgPP_col (N : ℕ) (hN : 4 ≤ N) (c : ℕ → Option Bool)
    (hc : ∀ j, 2 ≤ j → j < N → (c j).isSome = true) :
    Derivable (theory N) (mc N .hg [0, 1] c)
      (drawn [ppAt N 0 1, mc N .box [0] (setCtl c 1 (some true)), ppAt N 0 1]) :=
  hgPP N (by omega) c (by rw [hg_ctrl_len N (by omega) c hc]; omega)

theorem drawn3 {N : ℕ} (a b : Circ N) : drawn [a, b, a] = a * b * a := by simp [drawn, mul_assoc]

/-- A product of two gates between the same involution. -/
theorem conj_prod {N : ℕ} {P A B : Circ N} (hP : Derivable (theory N) (P * P) 1) :
    Derivable (theory N) (drawn [P * A * P, P * B * P]) (P * drawn [A, B] * P) := by
  rw [drawn2, drawn2]
  have e : P * B * P * (P * A * P) = P * B * (P * P) * A * P := by simp only [mul_assoc]
  rw [e]
  have h := dright P (dright A (dleft (P * B) hP))
  rw [mul_one] at h
  refine h.trans ?_
  simp only [mul_assoc]; exact Derivable.refl _

/-- (312) at width `N ≥ 4`, from (311). -/
theorem eq312_of {N : ℕ} (hN : 4 ≤ N) (ih : IH N)
    (h311 : ∀ x : ℕ → Bool, Derivable (theory N)
      (drawn [mc N .box [0] (colOn 1 N x), mc N .box [0] (colOn 1 N x)]) 1)
    (x : ℕ → Bool) :
    Derivable (theory N) (drawn [mc N .hg [0, 1] (colOn 2 N x), mc N .hg [0, 1] (colOn 2 N x)]) 1 := by
  have hP := pp_sq N (by omega) ih
  have h1 := hgPP_col N hN (colOn 2 N x) (fun j h2 hj => by simp [colOn, h2, hj])
  rw [drawn3] at h1
  set x' : ℕ → Bool := fun j => if j = 1 then true else x j
  have eB : mc N .box [0] (setCtl (colOn 2 N x) 1 (some true)) = mc N .box [0] (colOn 1 N x') :=
    mc_congr _ _ _ (fun i hi => by
      simp only [setCtl, colOn, x']
      split_ifs <;> first | rfl | omega)
  rw [eB] at h1
  have h2 := conj_prod (A := mc N .box [0] (colOn 1 N x')) (B := mc N .box [0] (colOn 1 N x')) hP
  rw [drawn2] at h2
  rw [drawn2]
  refine (dmul h1 h1).trans ?_
  refine h2.trans ?_
  have h3 := dright (ppAt N 0 1) (dleft (ppAt N 0 1) (h311 x'))
  rw [mul_one] at h3
  exact h3.trans hP

/-- (313) at width `N ≥ 4`, from (307). -/
theorem eq313_of {N : ℕ} (hN : 4 ≤ N)
    (h307 : ∀ j, 1 ≤ j → j + 2 ≤ N →
      Derivable (theory N) (drawn [BxI N, swAt N j]) (drawn [swAt N j, BxI N]))
    (j : ℕ) (hj : 2 ≤ j) (hjN : j + 2 ≤ N) :
    Derivable (theory N) (drawn [mc N .hg [0, 1] (blackOn 2 N), swAt N j])
      (drawn [swAt N j, mc N .hg [0, 1] (blackOn 2 N)]) := by
  have h1 := hgPP_col N hN (blackOn 2 N) (fun j h2 hj => by simp [blackOn, h2, hj])
  have eB : mc N .box [0] (setCtl (blackOn 2 N) 1 (some true)) = BxI N :=
    mc_congr _ _ _ (fun i hi => by
      simp only [setCtl, blackOn]
      split_ifs <;> first | rfl | omega)
  rw [eB] at h1
  set S := swAt N j
  have cP : Derivable (theory N) (S * ppAt N 0 1) (ppAt N 0 1 * S) :=
    pp_comm (by omega) (highW_mono (gLo_swAt N j) hj)
  have cB : Derivable (theory N) (S * BxI N) (BxI N * S) := by
    have := h307 j (by omega) hjN
    simpa [drawn] using this
  refine comm_drawn2 ((dleft S h1).trans ((comm_drawn S _ ?_).trans (dright S h1.symm)))
  intro y hy
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · exact cP
  · exact cB
  · exact cP

/-- Two controls among the wires `2, …`. -/
theorem hg_two (N : ℕ) (c : ℕ → Option Bool) (a b : ℕ) (hab : a ≠ b) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (haN : a < N) (hbN : b < N) (hca : (c a).isSome = true) (hcb : (c b).isSome = true) :
    2 ≤ (ctrlWires N [0, 1] c).length := by
  refine two_le_length ((List.nodup_range).filter _) hab ?_ ?_
  · simp only [ctrlWires, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
      List.contains_cons, List.contains_nil, Bool.or_eq_false_iff]
    exact ⟨haN, hca, by simp; omega, by simp; omega, trivial⟩
  · simp only [ctrlWires, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
      List.contains_cons, List.contains_nil, Bool.or_eq_false_iff]
    exact ⟨hbN, hcb, by simp; omega, by simp; omega, trivial⟩

/-- (310) at width `N ≥ 5`, from (309). -/
theorem eq310_of {N : ℕ} (hN : 5 ≤ N) (ih : IH N)
    (h309 : ∀ (x : ℕ → Bool) (w : ℕ), 1 ≤ w → w < N → ∀ b : Bool,
      Derivable (theory N)
        (drawn [mc N .box [0] (setCtl (colOn 1 N x) w (some b)),
          mc N .box [0] (setCtl (colOn 1 N x) w (some !b))])
        (mc N .box [0] (setCtl (colOn 1 N x) w none)))
    (x : ℕ → Bool) (w : ℕ) (hw : 2 ≤ w) (hwN : w < N) (b : Bool) :
    Derivable (theory N)
      (drawn [mc N .hg [0, 1] (setCtl (colOn 2 N x) w (some b)),
        mc N .hg [0, 1] (setCtl (colOn 2 N x) w (some !b))])
      (mc N .hg [0, 1] (setCtl (colOn 2 N x) w none)) := by
  have hP := pp_sq N (by omega) ih
  set x' : ℕ → Bool := fun j => if j = 1 then true else x j
  have hv : ∀ v : Option Bool, 2 ≤ (ctrlWires N [0, 1] (setCtl (colOn 2 N x) w v)).length →
      Derivable (theory N) (mc N .hg [0, 1] (setCtl (colOn 2 N x) w v))
        (ppAt N 0 1 * mc N .box [0] (setCtl (colOn 1 N x') w v) * ppAt N 0 1) := by
    intro v hk
    have h := hgPP N (by omega) _ hk
    rw [drawn3] at h
    refine h.trans (der_of_eq ?_)
    congr 2
    refine mc_congr _ _ _ (fun i hi => ?_)
    simp only [setCtl, colOn, x']
    split_ifs <;> first | rfl | omega
  have hk : ∀ v : Option Bool, 2 ≤ (ctrlWires N [0, 1] (setCtl (colOn 2 N x) w v)).length := by
    intro v
    let a := if w = 2 then 3 else 2
    let b' := if w = 4 then 3 else 4
    have ha : a ≠ w ∧ 2 ≤ a ∧ a < N := by simp only [a]; split_ifs <;> omega
    have hb : b' ≠ w ∧ 2 ≤ b' ∧ b' < N := by simp only [b']; split_ifs <;> omega
    have hab : a ≠ b' := by simp only [a, b']; split_ifs <;> omega
    refine hg_two N _ a b' hab ha.2.1 hb.2.1 ha.2.2 hb.2.2 ?_ ?_
    · simp [setCtl, colOn, ha.1, ha.2.1, ha.2.2]
    · simp [setCtl, colOn, hb.1, hb.2.1, hb.2.2]
  rw [drawn2]
  refine (dmul (hv (some !b) (hk _)) (hv (some b) (hk _))).trans ?_
  have hc := conj_prod (P := ppAt N 0 1) (A := mc N .box [0] (setCtl (colOn 1 N x') w (some b)))
    (B := mc N .box [0] (setCtl (colOn 1 N x') w (some !b))) hP
  rw [drawn2] at hc
  refine hc.trans ?_
  exact (dright _ (dleft _ (h309 x' w (by omega) hwN b))).trans (hv none (hk none)).symm

end QCert.RealCliffordCH.Sec8.D.N8

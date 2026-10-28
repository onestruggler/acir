/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (353): the swap of the wires `1, 2`, from four wires on, and the statement

See `E353.lean` for the argument.
-/
import QCert.RealCliffordCH.Sec8.D.N15.E353

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

/-- An equation between drawn products, conjugated by an involution factor by
factor. -/
theorem via_conj {N : ℕ} {u : Circ N} (hu : Derivable (theory N) (u * u) 1)
    {l r L R : List (Circ N)}
    (hl : List.Forall₂ (fun A B => Derivable (theory N) (u * A * u) B) l L)
    (hr : List.Forall₂ (fun A B => Derivable (theory N) (u * A * u) B) r R)
    (h : Derivable (theory N) (drawn l) (drawn r)) : Derivable (theory N) (drawn L) (drawn R) := by
  have m : ∀ {l L : List (Circ N)},
      List.Forall₂ (fun A B => Derivable (theory N) (u * A * u) B) l L →
      Derivable (theory N) (u * drawn l * u) (drawn L) := by
    intro l L hl
    refine (conj_drawn hu l).trans (drawn_forall2 ?_)
    induction hl with
    | nil => exact List.Forall₂.nil
    | cons h _ ih => exact List.Forall₂.cons h ih
  exact (m hl).symm.trans ((dctx u u h).trans (m hr))

section Four

variable (m : ℕ)

/-- The multi-controlled `H` of (333) with its box moved to wire `3`. -/
abbrev Hq : Circ (m + 4) :=
  mc (m + 4) .hg [3, 0] (ctlOr (ctlAt 1 true) (ctlOr (ctlAt 2 true) (blackOn 4 (m + 4))))
/-- The box of (333): box wire `1`, black on `0, 2, 3, …`. -/
abbrev Bq : Circ (m + 4) := mc (m + 4) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 4)))
/-- The same with wire `2` coloured `b`. -/
abbrev Bb (b : Bool) : Circ (m + 4) :=
  mc (m + 4) .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 b) (blackOn 3 (m + 4))))
/-- The same, idle on wire `2`. -/
abbrev Bi : Circ (m + 4) := mc (m + 4) .box [1] (ctlOr (ctlAt 0 true) (blackOn 3 (m + 4)))
/-- The box on wire `2`, black on `0, 3, …`, idle on wire `1`. -/
abbrev Bi' : Circ (m + 4) := mc (m + 4) .box [2] (ctlOr (ctlAt 0 true) (blackOn 3 (m + 4)))

theorem Bb_true : Bb m true = Bq m := Net.mc_congr _ _ _ (fun j hj => by
  rcases j with _ | _ | _ | j <;> simp [ctlOr, ctlAt, blackOn] <;> omega)

variable {m} (ih : IH (m + 4))
include ih

theorem sw0_inv : Derivable (theory (m + 4)) (swAt (m + 4) 0 * swAt (m + 4) 0) 1 :=
  swsw (m + 4) 0 (by omega)

/-- A box on wire `0` moved to wire `1` by the swap of the wires `0, 1`. -/
theorem box01 (c d : ℕ → Option Bool) (hcd : ∀ j < m + 4, d j = c (Net.tau 0 j)) :
    Derivable (theory (m + 4)) (swAt (m + 4) 0 * mc (m + 4) .box [0] c * swAt (m + 4) 0)
      (mc (m + 4) .box [1] d) := by
  have h := mcSwapBH ih 0 (by omega) .box (Or.inl rfl) [0] c rfl (by simp) (by simp)
  rw [conj3] at h
  refine h.trans (der_of_eq ?_)
  rw [show ([0] : List ℕ).map (Net.tau 0) = [1] by simp [Net.tau]]
  exact Net.mc_congr _ _ _ (fun j hj => (hcd j hj).symm)

/-- (309) for the box on wire `1`, merged on wire `2`. -/
theorem merge_Bb (b : Bool) : Derivable (theory (m + 4)) (drawn [Bb m b, Bb m (!b)]) (Bi m) := by
  have h := D.eq309 (m + 4) (by omega) ih (fun _ => true) 2 (by omega) (by omega) b
  have k := via_conj (sw0_inv ih) (L := [Bb m b, Bb m (!b)]) (R := [Bi m])
    (List.Forall₂.cons (box01 ih _ _ ?_) (List.Forall₂.cons (box01 ih _ _ ?_) List.Forall₂.nil))
    (List.Forall₂.cons (box01 ih _ _ ?_) List.Forall₂.nil) (by rwa [drawn_one'])
  · rwa [drawn_one'] at k
  all_goals
    intro j hj
    rcases j with _ | _ | _ | j <;> simp [Net.tau, setCtl, colOn, ctlOr, ctlAt, blackOn] <;> omega

/-- (311) for the box on wire `1` white on wire `2`. -/
theorem inv_Bw : Derivable (theory (m + 4)) (drawn [Bb m false, Bb m false]) 1 := by
  have h := D.eq311 (m + 4) (by omega) ih (fun j => decide (j ≠ 2))
  have k := via_conj (sw0_inv ih) (L := [Bb m false, Bb m false]) (R := [])
    (List.Forall₂.cons (box01 ih _ _ ?_) (List.Forall₂.cons (box01 ih _ _ ?_) List.Forall₂.nil))
    List.Forall₂.nil (by simpa [drawn] using h)
  · simpa [drawn] using k
  all_goals
    intro j hj
    rcases j with _ | _ | _ | j <;> simp [Net.tau, colOn, ctlOr, ctlAt, blackOn] <;> omega


/-- (339): the box white on wire `2` passes `Hq`. -/
theorem comm_Hq_Bw : D.Comm (m + 4) (Hq m) (Bb m false) := by
  have hsw := mcSwapBH ih
  have hnd : [1, 3, 0, 2].Nodup := by decide
  have hps : ∀ p ∈ [1, 3, 0, 2], p < m + 4 := by simp
  have f0 : frm [1, 3, 0, 2] 0 = 1 := frm_getD hnd hps (by simp)
  have f1 : frm [1, 3, 0, 2] 1 = 3 := frm_getD hnd hps (by simp)
  have f2 : frm [1, 3, 0, 2] 2 = 0 := frm_getD hnd hps (by simp)
  have f3 : frm [1, 3, 0, 2] 3 = 2 := frm_getD hnd hps (by simp)
  have hout : ∀ j, 4 ≤ j → j < m + 4 → 4 ≤ frm [1, 3, 0, 2] j ∧ frm [1, 3, 0, 2] j < m + 4 := by
    intro j hj hjN
    obtain ⟨hm, hl⟩ := frm_out' hnd hps (j := j) (by simpa using hj) hjN
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hm
    exact ⟨by omega, hl⟩
  have fB : Derivable (theory (m + 4)) (placedBy (m + 4) (netOf [1, 3, 0, 2])
      (mc (m + 4) .box [0] (ctlOr (ctlAt 2 true) (ctlOr (ctlAt 1 true)
        (colOn 3 (m + 4) fun j => decide (j ≠ 3)))))) (Bb m false) := by
    refine frameAtK hsw hnd hps .box (Or.inl rfl) [0] [1] _ _ rfl (by simp) (by simp)
      (by simp [f0]) (fun j hj => ?_)
    rcases j with _ | _ | _ | _ | j
    · simp [ctlOr, ctlAt, colOn, blackOn, f0]
    · simp [ctlOr, ctlAt, colOn, blackOn, f1]
    · simp [ctlOr, ctlAt, colOn, blackOn, f2]
    · simp [ctlOr, ctlAt, colOn, blackOn, f3]
    · obtain ⟨h4, hl⟩ := hout (j + 1 + 1 + 1 + 1) (by omega) hj
      simp [ctlOr, ctlAt, colOn, blackOn, hj, hl, show 3 ≤ frm [1, 3, 0, 2] (j + 1 + 1 + 1 + 1) by omega,
        show frm [1, 3, 0, 2] (j + 1 + 1 + 1 + 1) ≠ 0 by omega,
        show frm [1, 3, 0, 2] (j + 1 + 1 + 1 + 1) ≠ 2 by omega]
  have fH : Derivable (theory (m + 4)) (placedBy (m + 4) (netOf [1, 3, 0, 2])
      (mc (m + 4) .hg [1, 2] (ctlOr (ctlAt 0 true) (colOn 3 (m + 4) fun _ => true)))) (Hq m) := by
    refine frameAtK hsw hnd hps .hg (Or.inr rfl) [1, 2] [3, 0] _ _ rfl (by simp) (by simp)
      (by simp [f1, f2]) (fun j hj => ?_)
    rcases j with _ | _ | _ | _ | j
    · simp [ctlOr, ctlAt, colOn, blackOn, f0]
    · simp [ctlOr, ctlAt, colOn, blackOn, f1]
    · simp [ctlOr, ctlAt, colOn, blackOn, f2]
    · simp [ctlOr, ctlAt, colOn, blackOn, f3]
    · obtain ⟨h4, hl⟩ := hout (j + 1 + 1 + 1 + 1) (by omega) hj
      simp [ctlOr, ctlAt, colOn, blackOn, hj, hl, h4,
        show frm [1, 3, 0, 2] (j + 1 + 1 + 1 + 1) ≠ 1 by omega,
        show frm [1, 3, 0, 2] (j + 1 + 1 + 1 + 1) ≠ 2 by omega]
  have h := D.eq339 (m + 4) (by omega) ih (fun j => decide (j ≠ 3)) (fun _ => true)
    ⟨3, le_rfl, by omega, by simp⟩ true true true
  have k := via_frame hnd hps (List.Forall₂.cons fB (List.Forall₂.cons fH List.Forall₂.nil))
    (List.Forall₂.cons fH (List.Forall₂.cons fB List.Forall₂.nil)) h
  exact k.symm

/-- (274): the box idle on wire `2` moves its box wire to wire `2`. -/
theorem Bi_eq : Derivable (theory (m + 4)) (Bi m) (Bi' m) := by
  have hsw := mcSwapBH ih
  have hnd : [2, 1, 0].Nodup := by decide
  have hps : ∀ p ∈ [2, 1, 0], p < m + 4 := by simp
  have f0 : frm [2, 1, 0] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 1, 0] 1 = 1 := frm_getD hnd hps (by simp)
  have f2 : frm [2, 1, 0] 2 = 0 := frm_getD hnd hps (by simp)
  have hpt : ∀ j < m + 4, blackOn 2 (m + 4) j =
      (ctlOr (ctlAt 0 true) (blackOn 3 (m + 4))) (frm [2, 1, 0] j) := by
    intro j hj
    rcases j with _ | _ | _ | j
    · simp [ctlOr, ctlAt, blackOn, f0]
    · simp [ctlOr, ctlAt, blackOn, f1]
    · simp [ctlOr, ctlAt, blackOn, f2]
    · obtain ⟨hm, hl⟩ := frm_out' hnd hps (j := j + 1 + 1 + 1) (by simp) hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hm
      simp [ctlOr, ctlAt, blackOn, hj, hl, show 3 ≤ frm [2, 1, 0] (j + 1 + 1 + 1) by omega,
        show frm [2, 1, 0] (j + 1 + 1 + 1) ≠ 0 by omega]
  have f1' := frameAtK hsw hnd hps .box (Or.inl rfl) [1] [1] _ _ rfl (by simp) (by simp)
    (by simp [f1]) hpt
  have f0' := frameAtK hsw hnd hps .box (Or.inl rfl) [0] [2] _ _ rfl (by simp) (by simp)
    (by simp [f0]) hpt
  have h := D.eq274 (m + 4) (by omega) ih
  have k := via_frame hnd hps (l := [_]) (r := [_]) (List.Forall₂.cons f1' List.Forall₂.nil)
    (List.Forall₂.cons f0' List.Forall₂.nil) (by rwa [drawn_one', drawn_one'])
  rwa [drawn_one', drawn_one'] at k

/-- The `ZX` as `Hq Bq Hq Bq` ((333) and (353) for the wires `2, 3`). -/
theorem zx_Hq : Derivable (theory (m + 4)) (mc (m + 4) .zx [0] (blackOn 1 (m + 4)))
    (drawn [Hq m, Bq m, Hq m, Bq m]) := by
  have hsw := mcSwapBH ih
  have h333 := D.eq333 (m + 4) (by omega) ih
  have hS : Derivable (theory (m + 4)) (swAt (m + 4) 2 * swAt (m + 4) 2) 1 :=
    swsw (m + 4) 2 (by omega)
  have hZ : Derivable (theory (m + 4))
      (swAt (m + 4) 2 * mc (m + 4) .zx [0] (blackOn 1 (m + 4)) * swAt (m + 4) 2)
      (mc (m + 4) .zx [0] (blackOn 1 (m + 4))) :=
    conj_of_comm hS (comm_zx_sw_ge2 (m + 2) ih 2 le_rfl (by omega))
  have hH : Derivable (theory (m + 4))
      (swAt (m + 4) 2 * mc (m + 4) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 4))) *
        swAt (m + 4) 2) (Hq m) := by
    have h := hsw 2 (by omega) .hg (Or.inr rfl) [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 4))) rfl (by simp) (by simp)
    rw [conj3] at h
    refine h.trans (der_of_eq ?_)
    rw [show ([2, 0] : List ℕ).map (Net.tau 2) = [3, 0] by simp [Net.tau]]
    refine Net.mc_congr _ _ _ (fun j hj => ?_)
    rcases j with _ | _ | _ | _ | j <;> simp [Function.comp, Net.tau, ctlOr, ctlAt, blackOn] <;>
      omega
  have hB : Derivable (theory (m + 4)) (swAt (m + 4) 2 * Bq m * swAt (m + 4) 2) (Bq m) := by
    have h := hsw 2 (by omega) .box (Or.inl rfl) [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 4))) rfl (by simp) (by simp)
    rw [conj3] at h
    refine h.trans (der_of_eq ?_)
    rw [show ([1] : List ℕ).map (Net.tau 2) = [1] by simp [Net.tau]]
    refine Net.mc_congr _ _ _ (fun j hj => ?_)
    rcases j with _ | _ | _ | _ | j <;> simp [Function.comp, Net.tau, ctlOr, ctlAt, blackOn] <;>
      omega
  have k := via_conj hS (l := [mc (m + 4) .zx [0] (blackOn 1 (m + 4))]) (L := [_])
    (List.Forall₂.cons hZ List.Forall₂.nil)
    (List.Forall₂.cons hH (List.Forall₂.cons hB (List.Forall₂.cons hH (List.Forall₂.cons hB
      List.Forall₂.nil)))) (by rw [drawn_one']; exact h333)
  rwa [drawn_one'] at k

/-- `Hq Bq Hq Bq = Hq Bi Hq Bi` ((309), (339), (311)). -/
theorem Hq_Bi : Derivable (theory (m + 4)) (drawn [Hq m, Bq m, Hq m, Bq m])
    (drawn [Hq m, Bi m, Hq m, Bi m]) := by
  have m1 := merge_Bb ih true
  have m2 := merge_Bb ih false
  simp only [Bool.not_true, Bool.not_false] at m1 m2
  rw [drawn_two', Bb_true] at m1
  rw [drawn_two', Bb_true] at m2
  have hc := comm_Hq_Bw ih
  unfold D.Comm at hc
  rw [drawn_two', drawn_two'] at hc
  have hinv := inv_Bw ih
  rw [drawn_two'] at hinv
  rw [drawn_four', drawn_four']
  set H := Hq m
  set B := Bq m
  set W := Bb m false
  set I := Bi m
  -- `I H I H = (B W) H (W B) H = B (W H) W B H = B (H W) W B H = B H (W W) B H = B H B H`
  have e1 : Derivable (theory (m + 4)) (I * H * I * H) ((B * W) * H * (W * B) * H) :=
    dmul (dmul (dmul m2.symm (Derivable.refl _)) m1.symm) (Derivable.refl _)
  have e2 : (B * W) * H * (W * B) * H = B * (W * H) * W * B * H := by simp only [mul_assoc]
  have e3 : Derivable (theory (m + 4)) (B * (W * H) * W * B * H) (B * (H * W) * W * B * H) :=
    dright _ (dright _ (dright _ (dleft _ hc)))
  have e4 : B * (H * W) * W * B * H = B * H * (W * W) * B * H := by simp only [mul_assoc]
  have e5 : Derivable (theory (m + 4)) (B * H * (W * W) * B * H) (B * H * 1 * B * H) :=
    dright _ (dright _ (dleft _ hinv))
  have e6 : B * H * 1 * B * H = B * H * B * H := by rw [mul_one]
  exact ((e1.trans (der_of_eq e2)).trans (e3.trans ((der_of_eq e4).trans
    (e5.trans (der_of_eq e6))))).symm

/-- (353) for the `ZX` and the swap of the wires `1, 2`, from four wires on. -/
theorem comm_zx_sw_1 :
    D.Comm (m + 4) (mc (m + 4) .zx [0] (blackOn 1 (m + 4))) (swAt (m + 4) 1) := by
  have hsw := mcSwapBH ih
  have hS : Derivable (theory (m + 4)) (swAt (m + 4) 1 * swAt (m + 4) 1) 1 :=
    swsw (m + 4) 1 (by omega)
  have hH : Derivable (theory (m + 4)) (swAt (m + 4) 1 * Hq m * swAt (m + 4) 1) (Hq m) := by
    have h := hsw 1 (by omega) .hg (Or.inr rfl) [3, 0] (ctlOr (ctlAt 1 true) (ctlOr (ctlAt 2 true) (blackOn 4 (m + 4)))) rfl (by simp) (by simp)
    rw [conj3] at h
    refine h.trans (der_of_eq ?_)
    rw [show ([3, 0] : List ℕ).map (Net.tau 1) = [3, 0] by simp [Net.tau]]
    refine Net.mc_congr _ _ _ (fun j hj => ?_)
    rcases j with _ | _ | _ | _ | j <;> simp [Function.comp, Net.tau, ctlOr, ctlAt, blackOn] <;>
      omega
  have hB : Derivable (theory (m + 4)) (swAt (m + 4) 1 * Bi m * swAt (m + 4) 1) (Bi m) := by
    have h := hsw 1 (by omega) .box (Or.inl rfl) [1] (ctlOr (ctlAt 0 true) (blackOn 3 (m + 4))) rfl (by simp) (by simp)
    rw [conj3] at h
    refine h.trans (der_of_eq ?_) |>.trans (Bi_eq ih).symm
    rw [show ([1] : List ℕ).map (Net.tau 1) = [2] by simp [Net.tau]]
    refine Net.mc_congr _ _ _ (fun j hj => ?_)
    rcases j with _ | _ | _ | _ | j <;> simp [Function.comp, Net.tau, ctlOr, ctlAt, blackOn] <;>
      omega
  have hZ := (zx_Hq ih).trans (Hq_Bi ih)
  have k := via_conj hS (l := [mc (m + 4) .zx [0] (blackOn 1 (m + 4))]) (L := [_])
    (r := [_, _, _, _]) (R := [_, _, _, _])
    (List.Forall₂.cons (Derivable.refl _) List.Forall₂.nil)
    (List.Forall₂.cons hH (List.Forall₂.cons hB (List.Forall₂.cons hH (List.Forall₂.cons hB
      List.Forall₂.nil)))) (by rw [drawn_one']; exact hZ)
  rw [drawn_one'] at k
  exact comm_of_conj hS (k.trans hZ.symm)

end Four

/-! ## The statement -/

/-- (353) for the `ZX`. -/
theorem comm_zx_sw {N : ℕ} (hN : 3 ≤ N) (ih : IH N) (j : ℕ) (hj : 1 ≤ j) (hjN : j + 2 ≤ N) :
    D.Comm N (mc N .zx [0] (blackOn 1 N)) (swAt N j) := by
  rcases (by omega : 2 ≤ j ∨ j = 1) with hj2 | rfl
  · obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
    exact comm_zx_sw_ge2 k ih j hj2 hjN
  · rcases (by omega : N = 3 ∨ 4 ≤ N) with rfl | hN4
    · exact comm_zx_sw_3 ih
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 4 := ⟨N - 4, by omega⟩
      exact comm_zx_sw_1 ih

/-- (353): the multi-controlled `(-1)ᵃ ZX` commutes with the swap of two of
its controls. -/
theorem eq353 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (a : Bool) (j : ℕ) (hj : 1 ≤ j)
    (hjN : j + 2 ≤ N) :
    Derivable (theory N) (drawn [mc N (Kind.sgnZX a) [0] (blackOn 1 N), swAt N j])
      (drawn [swAt N j, mc N (Kind.sgnZX a) [0] (blackOn 1 N)]) := by
  have hz := comm_zx_sw hN ih j hj hjN
  cases a
  · exact hz
  · have h317 := D.eq317 N hN ih (fun _ => true)
    have e : ∀ K, mc N K [0] (colOn 1 N fun _ => true) = mc N K [0] (blackOn 1 N) := fun K =>
      Net.mc_congr _ _ _ (fun i hi => by simp [colOn, blackOn])
    rw [e, e, drawn_two', drawn_two'] at h317
    exact N13.Comm.inv hz h317.2 h317.1

end QCert.RealCliffordCH.Sec8.D.N15

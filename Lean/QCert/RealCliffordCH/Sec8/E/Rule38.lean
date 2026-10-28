/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rule (38)

For `a ≥ 4`, `G(a)` and `G(a + 1)` have a common bit `1` on a wire `w ≥ 2`
(`gray_common_one`; otherwise one of them would be a Gray code of `0, …, 3`).
So `D((-1)_[a]X_[a,a+1])`, the multi-controlled `ZX`/`XZ` on the wire `t` where
the two codes differ, has a black control on wire `w`, where the gadget
`D(H_[0,1]H_[3,2])` has a white one, and they commute by (348) (`t = 1`, the
box wire of the gadget), (349) (`t = 0`, its `H` wire) or (350) (`t ≥ 2`, a
control of the gadget), each moved to the wires of the gadget by a frame.
-/
import QCert.RealCliffordCH.Sec8.E.Rule39

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## The Gray code fact -/

theorem gray_small {n x : ℕ} (hn : 2 ≤ n) (hx : x < 2 ^ n)
    (h : ∀ w, 2 ≤ w → (gray x).testBit w = false) : x < 4 := by
  have hg : gray x < 2 ^ 2 := Nat.lt_pow_two_of_testBit _ (fun i hi => h i hi)
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨b, hb, hgb⟩ : ∃ b, b < 4 ∧ gray b = gray x := by
    have : gray x < 4 := by simpa using hg
    rcases (by omega : gray x = 0 ∨ gray x = 1 ∨ gray x = 2 ∨ gray x = 3) with e | e | e | e <;>
      rw [e]
    · exact ⟨0, by norm_num, by decide⟩
    · exact ⟨1, by norm_num, by decide⟩
    · exact ⟨3, by norm_num, by decide⟩
    · exact ⟨2, by norm_num, by decide⟩
  have := gray_inj (n := n) (by omega) hx hgb
  omega

/-- For `a ≥ 4`, `G(a)` has a bit `1` on a wire `w ≥ 2` other than the wire
where `G(a)` and `G(a + 1)` differ. -/
theorem gray_common_one {n a : ℕ} (h4 : 4 ≤ a) (ha : a + 1 < 2 ^ n) :
    ∃ w, 2 ≤ w ∧ w < n ∧ w ≠ tOf n a ∧ (gray a).testBit w = true := by
  have hn : 2 ≤ n := by
    by_contra hn
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_contra hne
  push Not at hne
  set t := tOf n a
  have hz : ∀ w, 2 ≤ w → w ≠ t → (gray a).testBit w = false := by
    intro w hw2 hwt
    by_cases hw : w < n
    · cases hb : (gray a).testBit w
      · rfl
      · exact absurd hb (by simp [hne w hw2 hw hwt])
    · exact testBit_of_lt (gray_lt (n := n) (by omega)) (by omega)
  have g1 := gray_succ_tOf (n := n) (a := a) ha
  by_cases ht : (gray a).testBit t = true ∧ 2 ≤ t
  · have : a + 1 < 4 := gray_small hn ha (fun w hw => by
      rw [g1]
      by_cases hwt : w = t
      · rw [hwt, testBit_xor_pow_self, ht.1]; rfl
      · rw [testBit_xor_pow_ne hwt]; exact hz w hw hwt)
    omega
  · have : a < 4 := gray_small hn (by omega) (fun w hw => by
      by_cases hwt : w = t
      · rw [hwt] at hw ⊢
        have : ¬ (gray a).testBit t = true := fun h => ht ⟨h, hw⟩
        simpa using this
      · exact hz w hw hwt)
    omega

/-! ## Frames at three wires -/

theorem frm_not_mem {N : ℕ} {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {j : ℕ}
    (hj : ps.length ≤ j) : frm ps j ∉ ps := by
  intro hm
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
  have h1 : frm ps i = ps[i] := by
    rw [frm_getD hnd hps hi]; simp [List.getD_eq_getElem?_getD, hi]
  have := frm_injective ps (h1.trans he)
  omega

/-- The colours of the canonical gate for a gate whose wires are `ps`. -/
def pullL (ps : List ℕ) (s : ℕ) : ℕ → Bool := fun j => decide (bitOf s (frm ps j) = 1)

theorem bitOf_decide (s w : ℕ) : decide (bitOf s w = 1) = s.testBit w := by
  rw [bitOf_eq]; cases s.testBit w <;> rfl

/-- A black control on wire `w` (outside `ps`) gives a black canonical control
above the special wires. -/
theorem pullL_black {N : ℕ} {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {s w : ℕ}
    (hw : w < N) (hwps : w ∉ ps) (hs : s.testBit w = true) :
    ps.length ≤ pos (netOf ps) w ∧ pos (netOf ps) w < N ∧ pullL ps s (pos (netOf ps) w) = true := by
  refine ⟨?_, pos_lt _ (netOf_ok hnd hps) w hw, ?_⟩
  · by_contra hlt
    push Not at hlt
    apply hwps
    rw [← frm_pos ps w, frm_getD hnd hps hlt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlt]
    exact List.getElem_mem hlt
  · simp only [pullL, frm_pos, bitOf_decide, hs]


/-- A frame, with the canonical colours given pointwise. -/
theorem frameAt {N : ℕ} (hsw : McSwapAll N) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p < N) (K : Kind) (tg tg' : List ℕ) (c d : ℕ → Option Bool)
    (hl : tg.length = kindSp K) (htnd : tg.Nodup) (htN : ∀ t ∈ tg, t < N)
    (htg : tg.map (frm ps) = tg') (h : ∀ j < N, d j = c (frm ps j)) :
    Derivable (theory N) (placedBy N (netOf ps) (mc N K tg d)) (mc N K tg' c) := by
  rw [Net.mc_congr N K tg (c := d) (c' := c ∘ frm ps) h, ← htg]
  exact frame hsw hnd hps K tg c hl htnd htN

/-- Outside the special wires `ps` the frame stays outside `ps`. -/
theorem frm_out {N : ℕ} {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {j : ℕ}
    (hj : ps.length ≤ j) (hjN : j < N) : frm ps j ∉ ps ∧ frm ps j < N :=
  ⟨frm_not_mem hnd hps hj, frm_lt hnd hps hjN⟩

/-! ## The rule -/

/-- The decoded `ZX` letter commutes with the gadget when it has a black
control on a wire `w ≥ 2`. -/
theorem zx_gadget_comm {M : ℕ} (ih : IH (M + 3)) (γ : Bool) {t s w : ℕ} (ht : t < M + 3)
    (hw2 : 2 ≤ w) (hwN : w < M + 3) (hwt : w ≠ t) (hs : s.testBit w = true) :
    D.Comm (M + 3) (mc (M + 3) .hg [1, 0] (colOn 2 (M + 3) fun _ => false))
      (mc (M + 3) (Kind.sgnZX γ) [t] (ctlOf s t)) := by
  have hK : kindSp (Kind.sgnZX γ) = 1 := by cases γ <;> rfl
  have hsw := mcSwapAll ih
  have hnd2 : [1, 0].Nodup := by simp
  have hps2 : ∀ p ∈ [1, 0], p < M + 3 := by simp
  have g0 : frm [1, 0] 0 = 1 := frm_getD hnd2 hps2 (by simp)
  have g1 : frm [1, 0] 1 = 0 := frm_getD hnd2 hps2 (by simp)
  -- the gadget at the canonical position of the frame `[1, 0]`
  have fG : Derivable (theory (M + 3))
      (placedBy (M + 3) (netOf [1, 0]) (mc (M + 3) .hg [0, 1] (colOn 2 (M + 3) fun _ => false)))
      (mc (M + 3) .hg [1, 0] (colOn 2 (M + 3) fun _ => false)) := by
    refine frameAt hsw hnd2 hps2 .hg [0, 1] [1, 0] _ _ rfl (by simp) (by simp)
      (by simp [g0, g1]) (fun j hj => ?_)
    rcases j with _ | _ | j
    · simp [colOn, g0]
    · simp [colOn, g1]
    · obtain ⟨hm, hl⟩ := frm_out hnd2 hps2 (j := j + 1 + 1) (by simp) hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      have h2 : 2 ≤ frm [1, 0] (j + 1 + 1) := by omega
      simp [colOn, hj, hl, h2]
  rcases (by omega : t = 0 ∨ t = 1 ∨ 2 ≤ t) with rfl | rfl | ht2
  · -- `t = 0`: the `H` wire of the gadget, (349)
    have fZ : Derivable (theory (M + 3))
        (placedBy (M + 3) (netOf [1, 0]) (mc (M + 3) (Kind.sgnZX γ) [1]
          (ctlOr (ctlAt 0 (decide (bitOf s 1 = 1))) (colOn 2 (M + 3) (pullL [1, 0] s)))))
        (mc (M + 3) (Kind.sgnZX γ) [0] (ctlOf s 0)) := by
      refine frameAt hsw hnd2 hps2 (Kind.sgnZX γ) [1] [0] _ _ (by simp [hK]) (by simp)
        (by simp) (by simp [g1]) (fun j hj => ?_)
      rcases j with _ | _ | j
      · simp [ctlOr, ctlAt, colOn, ctlOf, g0]
      · simp [ctlOr, ctlAt, colOn, ctlOf, g1]
      · obtain ⟨hm, _⟩ := frm_out hnd2 hps2 (j := j + 1 + 1) (by simp) hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
        simp [ctlOr, ctlAt, colOn, ctlOf, hm.2, pullL, hj]
    obtain ⟨hp2, hpN, hpy⟩ := pullL_black hnd2 hps2 hwN (by simp; omega) hs
    have hd : DiffOn 2 (M + 3) (fun _ => false) (pullL [1, 0] s) :=
      ⟨_, by simpa using hp2, hpN, by rw [hpy]; simp⟩
    exact via_frame hnd2 hps2 (List.Forall₂.cons fG (List.Forall₂.cons fZ List.Forall₂.nil))
      (List.Forall₂.cons fZ (List.Forall₂.cons fG List.Forall₂.nil))
      (D.eq349 (M + 3) (by omega) ih _ _ hd γ _)
  · -- `t = 1`: the box wire of the gadget, (348)
    have fZ : Derivable (theory (M + 3))
        (placedBy (M + 3) (netOf [1, 0]) (mc (M + 3) (Kind.sgnZX γ) [0]
          (ctlOr (ctlAt 1 (decide (bitOf s 0 = 1))) (colOn 2 (M + 3) (pullL [1, 0] s)))))
        (mc (M + 3) (Kind.sgnZX γ) [1] (ctlOf s 1)) := by
      refine frameAt hsw hnd2 hps2 (Kind.sgnZX γ) [0] [1] _ _ (by simp [hK]) (by simp)
        (by simp) (by simp [g0]) (fun j hj => ?_)
      rcases j with _ | _ | j
      · simp [ctlOr, ctlAt, colOn, ctlOf, g0]
      · simp [ctlOr, ctlAt, colOn, ctlOf, g1]
      · obtain ⟨hm, _⟩ := frm_out hnd2 hps2 (j := j + 1 + 1) (by simp) hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
        simp [ctlOr, ctlAt, colOn, ctlOf, hm.1, pullL, hj]
    obtain ⟨hp2, hpN, hpy⟩ := pullL_black hnd2 hps2 hwN (by simp; omega) hs
    have hd : DiffOn 2 (M + 3) (fun _ => false) (pullL [1, 0] s) :=
      ⟨_, by simpa using hp2, hpN, by rw [hpy]; simp⟩
    exact via_frame hnd2 hps2 (List.Forall₂.cons fG (List.Forall₂.cons fZ List.Forall₂.nil))
      (List.Forall₂.cons fZ (List.Forall₂.cons fG List.Forall₂.nil))
      (D.eq348 (M + 3) (by omega) ih _ _ hd γ _)
  · -- `t ≥ 2`: a control of the gadget, (350)
    have hnd3 : [1, 0, t].Nodup := by simp; omega
    have hps3 : ∀ p ∈ [1, 0, t], p < M + 3 := by simp; omega
    have h0 : frm [1, 0, t] 0 = 1 := frm_getD hnd3 hps3 (by simp)
    have h1 : frm [1, 0, t] 1 = 0 := frm_getD hnd3 hps3 (by simp)
    have h2 : frm [1, 0, t] 2 = t := frm_getD hnd3 hps3 (by simp)
    have fG3 : Derivable (theory (M + 3))
        (placedBy (M + 3) (netOf [1, 0, t])
          (mc (M + 3) .hg [0, 1] (ctlOr (ctlAt 2 false) (colOn 3 (M + 3) fun _ => false))))
        (mc (M + 3) .hg [1, 0] (colOn 2 (M + 3) fun _ => false)) := by
      refine frameAt hsw hnd3 hps3 .hg [0, 1] [1, 0] _ _ rfl (by simp) (by simp)
        (by simp [h0, h1]) (fun j hj => ?_)
      rcases j with _ | _ | _ | j
      · simp [ctlOr, ctlAt, colOn, h0]
      · simp [ctlOr, ctlAt, colOn, h1]
      · simp [ctlOr, ctlAt, colOn, h2, ht2, ht]
      · obtain ⟨hm, hl⟩ := frm_out hnd3 hps3 (j := j + 1 + 1 + 1) (by simp) hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
        have h2' : 2 ≤ frm [1, 0, t] (j + 1 + 1 + 1) := by omega
        simp [ctlOr, ctlAt, colOn, hj, hl, h2']
    have fZ3 : Derivable (theory (M + 3))
        (placedBy (M + 3) (netOf [1, 0, t]) (mc (M + 3) (Kind.sgnZX γ) [2]
          (ctlOr (ctlAt 1 (decide (bitOf s 0 = 1)))
            (ctlOr (ctlAt 0 (decide (bitOf s 1 = 1))) (colOn 3 (M + 3) (pullL [1, 0, t] s))))))
        (mc (M + 3) (Kind.sgnZX γ) [t] (ctlOf s t)) := by
      refine frameAt hsw hnd3 hps3 (Kind.sgnZX γ) [2] [t] _ _ (by simp [hK]) (by simp)
        (by simp) (by simp [h2]) (fun j hj => ?_)
      rcases j with _ | _ | _ | j
      · simp [ctlOr, ctlAt, colOn, ctlOf, h0, show (1 : ℕ) ≠ t by omega]
      · simp [ctlOr, ctlAt, colOn, ctlOf, h1, show (0 : ℕ) ≠ t by omega]
      · simp [ctlOr, ctlAt, colOn, ctlOf, h2]
      · obtain ⟨hm, _⟩ := frm_out hnd3 hps3 (j := j + 1 + 1 + 1) (by simp) hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
        simp [ctlOr, ctlAt, colOn, ctlOf, hm.2.2, pullL, hj]
    obtain ⟨hp3, hpN, hpy⟩ := pullL_black hnd3 hps3 hwN (by simp; omega) hs
    have hd : DiffOn 3 (M + 3) (fun _ => false) (pullL [1, 0, t] s) :=
      ⟨_, by simpa using hp3, hpN, by rw [hpy]; simp⟩
    exact via_frame hnd3 hps3 (List.Forall₂.cons fG3 (List.Forall₂.cons fZ3 List.Forall₂.nil))
      (List.Forall₂.cons fZ3 (List.Forall₂.cons fG3 List.Forall₂.nil))
      (D.eq350 (M + 3) (by omega) ih _ _ hd γ _ _ _)

/-- (38) decodes to (348), (349) or (350). -/
theorem dec38 {M : ℕ} (ih : IH (M + 3)) (a : ℕ) (h4 : 4 ≤ a) (ha : a + 1 < 2 ^ (M + 3)) :
    Derivable (theory (M + 3))
      (decW (M + 3) (wordOf [Zx (M + 3) a a (a + 1), Hh (M + 3) 0 1 3 2]))
      (decW (M + 3) (wordOf [Hh (M + 3) 0 1 3 2, Zx (M + 3) a a (a + 1)])) := by
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_0132 (by omega : 3 ≤ M + 3), gadget_colOn, dec_Zx_lo ha]
  rw [dZX1_mc (M + 2)]
  obtain ⟨γ, hγ⟩ := kindZX_sgn (k := M + 2) (a := a) 0
  rw [hγ]
  obtain ⟨w, hw2, hwN, hwt, hs⟩ := gray_common_one (n := M + 2 + 1) h4 ha
  have h := zx_gadget_comm ih γ (tOf_lt a (by omega)) hw2 hwN hwt hs
  unfold D.Comm at h
  rw [drawn_two, drawn_two] at h
  exact h

end QCert.RealCliffordCH.Sec8.E

/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (354): a black and a white control of the multi-controlled `ZX` merge

The paper's proof.  On the top wire `T`, every other control black: by (333)
each of the two gates is `H B H B` (`H` the multi-controlled `H` on wire `0`
with its box on wire `2`, `B` the box on wire `1`), the white one conjugated by
`X` on wire `T` ((81)); every gate of one expansion commutes with every gate
of the other ((335), (340), (339): opposite colours on wire `T`), so the
product shuffles into `(H H')(B B')(H H')(B B')`, whose pairs merge ((310),
(309)) into gates idle on wire `T`, which form the `ZX` idle on wire `T` by
(333) one wire down (`merge_top_core`).  The colours of the other controls
follow by (81) (`merge_top`), any wire by (353) (`merge_any`), and the `XZ` as
the inverse of the `ZX` ((317), Lemma B.5).  On three wires the core is (136),
(137).
-/
import QCert.RealCliffordCH.Sec8.D.N15.Swap

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

section Core

variable (m : ℕ)

/-- The controls of the multi-controlled `H` of (333), wire `m + 3` set to `v`. -/
def cH (v : Option Bool) : ℕ → Option Bool :=
  setCtl (ctlOr (ctlAt 1 true) (blackOn 3 (m + 4))) (m + 3) v
/-- The controls of the box of (333), wire `m + 3` set to `v`. -/
def cB (v : Option Bool) : ℕ → Option Bool :=
  setCtl (ctlOr (ctlAt 0 true) (blackOn 2 (m + 4))) (m + 3) v
/-- The controls of the `ZX`, wire `m + 3` set to `v`. -/
def cZ (v : Option Bool) : ℕ → Option Bool := setCtl (blackOn 1 (m + 4)) (m + 3) v

abbrev Hc (v : Option Bool) : Circ (m + 4) := mc (m + 4) .hg [2, 0] (cH m v)
abbrev Bc (v : Option Bool) : Circ (m + 4) := mc (m + 4) .box [1] (cB m v)
abbrev Zc (v : Option Bool) : Circ (m + 4) := mc (m + 4) .zx [0] (cZ m v)

theorem setCtl_setCtl (c : ℕ → Option Bool) (w : ℕ) (v v' : Option Bool) :
    setCtl (setCtl c w v) w v' = setCtl c w v' := by
  funext j; simp only [setCtl]; split_ifs <;> rfl

variable {m} (ih : IH (m + 4))
include ih

/-- (333) for the gates black, then white, on wire `m + 3`. -/
theorem exp333 (b : Bool) :
    Derivable (theory (m + 4)) (Zc m (some b))
      (drawn [Hc m (some b), Bc m (some b), Hc m (some b), Bc m (some b)]) := by
  have h333 := D.eq333 (m + 4) (by omega) ih
  have eZ : mc (m + 4) .zx [0] (blackOn 1 (m + 4)) = Zc m (some true) :=
    Net.mc_congr _ _ _ (fun j hj => by
      simp only [cZ, setCtl, blackOn]; split_ifs <;> first | rfl | omega)
  have eH : mc (m + 4) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 4))) = Hc m (some true) :=
    Net.mc_congr _ _ _ (fun j hj => by
      simp only [cH, setCtl, ctlOr, ctlAt, blackOn]; split_ifs <;> first | rfl | omega)
  have eB : mc (m + 4) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 4))) = Bc m (some true) :=
    Net.mc_congr _ _ _ (fun j hj => by
      simp only [cB, setCtl, ctlOr, ctlAt, blackOn]; split_ifs <;> first | rfl | omega)
  rw [eZ, eH, eB] at h333
  cases b
  · have hx := D.xAt_inv (m + 4) (m + 3) (by omega)
    have fl : ∀ (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool), m + 3 ∉ tg →
        c (m + 3) = some true →
        Derivable (theory (m + 4)) (xAt (m + 4) (m + 3) * mc (m + 4) K tg c * xAt (m + 4) (m + 3))
          (mc (m + 4) K tg (setCtl c (m + 3) (some false))) := by
      intro K tg c ht hc
      have := D.eq81 (m + 4) K tg c (m + 3) true (by omega) ht hc
      rwa [conj3] at this
    have hZ := fl .zx [0] (cZ m (some true)) (by simp) (by simp [cZ, setCtl])
    have hH := fl .hg [2, 0] (cH m (some true)) (by simp) (by simp [cH, setCtl])
    have hB := fl .box [1] (cB m (some true)) (by simp) (by simp [cB, setCtl])
    simp only [cZ, cH, cB, setCtl_setCtl] at hZ hH hB
    have k := via_conj hx (l := [Zc m (some true)]) (L := [Zc m (some false)])
      (List.Forall₂.cons hZ List.Forall₂.nil)
      (List.Forall₂.cons hH (List.Forall₂.cons hB (List.Forall₂.cons hH (List.Forall₂.cons hB
        List.Forall₂.nil)))) (by rw [drawn_one']; exact h333)
    rwa [drawn_one'] at k
  · exact h333


/-! ## The pieces -/


theorem comm_HH (b b' : Bool) : D.Comm (m + 4) (Hc m (some b)) (Hc m (some b')) := by
  have hnd : [2, 0, 1].Nodup := by decide
  have hps : ∀ p ∈ [2, 0, 1], p < m + 4 := by simp
  have f0 : frm [2, 0, 1] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 0, 1] 1 = 0 := frm_getD hnd hps (by simp)
  have f2 : frm [2, 0, 1] 2 = 1 := frm_getD hnd hps (by simp)
  have hk : ∀ i, i < 3 ↔ i ∈ [2, 0, 1] := by intro i; simp; omega
  have fr : ∀ b, Derivable (theory (m + 4)) (placedBy (m + 4) (netOf [2, 0, 1])
      (mc (m + 4) .hg [0, 1] (colOn 2 (m + 4) (colT [2, 0, 1] (m + 3) b)))) (Hc m (some b)) := by
    intro b
    refine frameAt' ih hnd hps .hg [0, 1] [2, 0] _ _ rfl (by simp) (by simp) (by simp [f0, f1])
      (fun j hj => ?_)
    rcases j with _ | _ | _ | j
    · simp [colOn, cH, setCtl, ctlOr, ctlAt, blackOn, f0]
    · simp [colOn, cH, setCtl, ctlOr, ctlAt, blackOn, f1]
    · simp [colOn, colT, cH, setCtl, ctlOr, ctlAt, blackOn, f2]
    · obtain ⟨h3, hl⟩ := frm_ge hnd hps 3 hk (j := j + 1 + 1 + 1) (by simp) hj
      simp only [colOn, colT, cH, setCtl, ctlOr, ctlAt, blackOn]
      split_ifs <;> first | rfl | omega
  exact comm_frame hnd hps (fr b) (fr b') (D.eq340 (m + 4) (by omega) ih _ _)

theorem comm_BB (b b' : Bool) : D.Comm (m + 4) (Bc m (some b)) (Bc m (some b')) := by
  have hnd : [1, 0].Nodup := by decide
  have hps : ∀ p ∈ [1, 0], p < m + 4 := by simp
  have f0 : frm [1, 0] 0 = 1 := frm_getD hnd hps (by simp)
  have f1 : frm [1, 0] 1 = 0 := frm_getD hnd hps (by simp)
  have hk : ∀ i, i < 2 ↔ i ∈ [1, 0] := by intro i; simp; omega
  have fr : ∀ b, Derivable (theory (m + 4)) (placedBy (m + 4) (netOf [1, 0])
      (mc (m + 4) .box [0] (colOn 1 (m + 4) (colT [1, 0] (m + 3) b)))) (Bc m (some b)) := by
    intro b
    refine frameAt' ih hnd hps .box [0] [1] _ _ rfl (by simp) (by simp) (by simp [f0])
      (fun j hj => ?_)
    rcases j with _ | _ | j
    · simp [colOn, cB, setCtl, ctlOr, ctlAt, blackOn, f0]
    · simp [colOn, colT, cB, setCtl, ctlOr, ctlAt, blackOn, f1]
    · obtain ⟨h2, hl⟩ := frm_ge hnd hps 2 hk (j := j + 1 + 1) (by simp) hj
      simp only [colOn, colT, cB, setCtl, ctlOr, ctlAt, blackOn]
      split_ifs <;> first | rfl | omega
  exact comm_frame hnd hps (fr b) (fr b') (D.eq335 (m + 4) (by omega) ih _ _)

theorem comm_BH (b : Bool) : D.Comm (m + 4) (Bc m (some b)) (Hc m (some !b)) := by
  have hnd : [1, 2, 0].Nodup := by decide
  have hps : ∀ p ∈ [1, 2, 0], p < m + 4 := by simp
  have f0 : frm [1, 2, 0] 0 = 1 := frm_getD hnd hps (by simp)
  have f1 : frm [1, 2, 0] 1 = 2 := frm_getD hnd hps (by simp)
  have f2 : frm [1, 2, 0] 2 = 0 := frm_getD hnd hps (by simp)
  have hk : ∀ i, i < 3 ↔ i ∈ [1, 2, 0] := by intro i; simp; omega
  have fB : Derivable (theory (m + 4)) (placedBy (m + 4) (netOf [1, 2, 0])
      (mc (m + 4) .box [0] (ctlOr (ctlAt 2 true) (ctlOr (ctlAt 1 true)
        (colOn 3 (m + 4) (colT [1, 2, 0] (m + 3) b)))))) (Bc m (some b)) := by
    refine frameAt' ih hnd hps .box [0] [1] _ _ rfl (by simp) (by simp) (by simp [f0])
      (fun j hj => ?_)
    rcases j with _ | _ | _ | j
    · simp [colOn, cB, setCtl, ctlOr, ctlAt, blackOn, f0]
    · simp [colOn, cB, setCtl, ctlOr, ctlAt, blackOn, f1]
    · simp [colOn, cB, setCtl, ctlOr, ctlAt, blackOn, f2]
    · obtain ⟨h3, hl⟩ := frm_ge hnd hps 3 hk (j := j + 1 + 1 + 1) (by simp) hj
      simp only [colOn, colT, cB, setCtl, ctlOr, ctlAt, blackOn]
      split_ifs <;> first | rfl | omega
  have fH : Derivable (theory (m + 4)) (placedBy (m + 4) (netOf [1, 2, 0])
      (mc (m + 4) .hg [1, 2] (ctlOr (ctlAt 0 true) (colOn 3 (m + 4) (colT [1, 2, 0] (m + 3) !b)))))
      (Hc m (some !b)) := by
    refine frameAt' ih hnd hps .hg [1, 2] [2, 0] _ _ rfl (by simp) (by simp) (by simp [f1, f2])
      (fun j hj => ?_)
    rcases j with _ | _ | _ | j
    · simp [colOn, cH, setCtl, ctlOr, ctlAt, blackOn, f0]
    · simp [colOn, cH, setCtl, ctlOr, ctlAt, blackOn, f1]
    · simp [colOn, cH, setCtl, ctlOr, ctlAt, blackOn, f2]
    · obtain ⟨h3, hl⟩ := frm_ge hnd hps 3 hk (j := j + 1 + 1 + 1) (by simp) hj
      simp only [colOn, colT, ctlOr, ctlAt]
      generalize frm [1, 2, 0] (j + 1 + 1 + 1) = f at h3 hl ⊢
      by_cases hf : f = m + 3
      · simp [colOn, colT, cH, setCtl, ctlOr, ctlAt, blackOn, hf, hj]
      · simp [colOn, colT, cH, setCtl, ctlOr, ctlAt, blackOn, hf, hj, hl,
          show f ≠ 1 by omega, show 3 ≤ f by omega]
  obtain ⟨hp3, hpN⟩ := pos_ge hnd hps (w := m + 3) (by omega) (by simp)
  have hd : DiffOn 3 (m + 4) (colT [1, 2, 0] (m + 3) b) (colT [1, 2, 0] (m + 3) !b) :=
    ⟨_, by simpa using hp3, hpN, by simp [colT, frm_pos]⟩
  exact comm_frame hnd hps fB fH (D.eq339 (m + 4) (by omega) ih _ _ hd true true true)

theorem comm_HB (b : Bool) : D.Comm (m + 4) (Hc m (some b)) (Bc m (some !b)) := by
  have h := comm_BH ih (!b)
  rw [Bool.not_not] at h
  exact h.symm

/-- (310) on wire `m + 3`. -/
theorem merge_HH (b : Bool) :
    Derivable (theory (m + 4)) (drawn [Hc m (some b), Hc m (some !b)]) (Hc m none) := by
  have hnd : [2, 0, 1].Nodup := by decide
  have hps : ∀ p ∈ [2, 0, 1], p < m + 4 := by simp
  have f0 : frm [2, 0, 1] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 0, 1] 1 = 0 := frm_getD hnd hps (by simp)
  have f2 : frm [2, 0, 1] 2 = 1 := frm_getD hnd hps (by simp)
  have hk : ∀ i, i < 3 ↔ i ∈ [2, 0, 1] := by intro i; simp; omega
  obtain ⟨hp3, hpN⟩ := pos_ge hnd hps (w := m + 3) (by omega) (by simp)
  have fr : ∀ v, Derivable (theory (m + 4)) (placedBy (m + 4) (netOf [2, 0, 1])
      (mc (m + 4) .hg [0, 1] (setCtl (colOn 2 (m + 4) fun _ => true)
        (pos (netOf [2, 0, 1]) (m + 3)) v))) (Hc m v) := by
    intro v
    refine frameAt' ih hnd hps .hg [0, 1] [2, 0] _ _ rfl (by simp) (by simp) (by simp [f0, f1])
      (fun j hj => ?_)
    rw [cH, setCtl_frm']
    by_cases hjw : j = pos (netOf [2, 0, 1]) (m + 3)
    · simp only [setCtl, if_pos hjw]
    · simp only [setCtl, if_neg hjw, Function.comp]
      rcases j with _ | _ | _ | j
      · simp [colOn, ctlOr, ctlAt, blackOn, f0]
      · simp [colOn, ctlOr, ctlAt, blackOn, f1]
      · simp [colOn, ctlOr, ctlAt, blackOn, f2]
      · obtain ⟨h3, hl⟩ := frm_ge hnd hps 3 hk (j := j + 1 + 1 + 1) (by simp) hj
        generalize frm [2, 0, 1] (j + 1 + 1 + 1) = f at h3 hl ⊢
        simp [colOn, ctlOr, ctlAt, blackOn, hj, hl, show f ≠ 1 by omega, show 3 ≤ f by omega]
  have h := D.eq310 (m + 4) (by omega) ih (fun _ => true) (pos (netOf [2, 0, 1]) (m + 3))
    (by simp at hp3; omega) hpN b
  have k := via_frame hnd hps (L := [Hc m (some b), Hc m (some !b)]) (R := [Hc m none])
    (List.Forall₂.cons (fr _) (List.Forall₂.cons (fr _) List.Forall₂.nil))
    (List.Forall₂.cons (fr _) List.Forall₂.nil) (by rwa [drawn_one'])
  rwa [drawn_one'] at k

/-- (309) on wire `m + 3`. -/
theorem merge_BB (b : Bool) :
    Derivable (theory (m + 4)) (drawn [Bc m (some b), Bc m (some !b)]) (Bc m none) := by
  have hnd : [1, 0].Nodup := by decide
  have hps : ∀ p ∈ [1, 0], p < m + 4 := by simp
  have f0 : frm [1, 0] 0 = 1 := frm_getD hnd hps (by simp)
  have f1 : frm [1, 0] 1 = 0 := frm_getD hnd hps (by simp)
  have hk : ∀ i, i < 2 ↔ i ∈ [1, 0] := by intro i; simp; omega
  obtain ⟨hp2, hpN⟩ := pos_ge hnd hps (w := m + 3) (by omega) (by simp)
  have fr : ∀ v, Derivable (theory (m + 4)) (placedBy (m + 4) (netOf [1, 0])
      (mc (m + 4) .box [0] (setCtl (colOn 1 (m + 4) fun _ => true)
        (pos (netOf [1, 0]) (m + 3)) v))) (Bc m v) := by
    intro v
    refine frameAt' ih hnd hps .box [0] [1] _ _ rfl (by simp) (by simp) (by simp [f0])
      (fun j hj => ?_)
    rw [cB, setCtl_frm']
    by_cases hjw : j = pos (netOf [1, 0]) (m + 3)
    · simp only [setCtl, if_pos hjw]
    · simp only [setCtl, if_neg hjw, Function.comp]
      rcases j with _ | _ | j
      · simp [colOn, ctlOr, ctlAt, blackOn, f0]
      · simp [colOn, ctlOr, ctlAt, blackOn, f1]
      · obtain ⟨h2, hl⟩ := frm_ge hnd hps 2 hk (j := j + 1 + 1) (by simp) hj
        generalize frm [1, 0] (j + 1 + 1) = f at h2 hl ⊢
        simp [colOn, ctlOr, ctlAt, blackOn, hj, hl, show f ≠ 0 by omega, show 2 ≤ f by omega]
  have h := D.eq309 (m + 4) (by omega) ih (fun _ => true) (pos (netOf [1, 0]) (m + 3))
    (by simp at hp2; omega) hpN b
  have k := via_frame hnd hps (L := [Bc m (some b), Bc m (some !b)]) (R := [Bc m none])
    (List.Forall₂.cons (fr _) (List.Forall₂.cons (fr _) List.Forall₂.nil))
    (List.Forall₂.cons (fr _) List.Forall₂.nil) (by rwa [drawn_one'])
  rwa [drawn_one'] at k

/-- (333) one wire down, for the gates idle on wire `m + 3`. -/
theorem exp333_idle :
    Derivable (theory (m + 4)) (drawn [Hc m none, Bc m none, Hc m none, Bc m none]) (Zc m none) := by
  have h := derivable_padTop (D.eq333 (m + 3) (by omega) (ih.mono (by omega)))
  rw [← drawn_map_padTop] at h
  simp only [List.map_cons, List.map_nil] at h
  have eZ : padTop (mc (m + 3) .zx [0] (blackOn 1 (m + 3))) = Zc m none := by
    rw [← mc_top (m + 3) .zx [0] _ rfl (by simp) (by simp) (by simp [blackOn])]
    exact Net.mc_congr _ _ _ (fun j hj => by
      simp only [cZ, setCtl, blackOn]; split_ifs <;> first | rfl | omega)
  have eH : padTop (mc (m + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 3)))) = Hc m none := by
    rw [← mc_top (m + 3) .hg [2, 0] _ rfl (by simp) (by simp) (by simp [ctlOr, ctlAt, blackOn])]
    exact Net.mc_congr _ _ _ (fun j hj => by
      simp only [cH, setCtl, ctlOr, ctlAt, blackOn]; split_ifs <;> first | rfl | omega)
  have eB : padTop (mc (m + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 3)))) = Bc m none := by
    rw [← mc_top (m + 3) .box [1] _ rfl (by simp) (by simp) (by simp [ctlOr, ctlAt, blackOn])]
    exact Net.mc_congr _ _ _ (fun j hj => by
      simp only [cB, setCtl, ctlOr, ctlAt, blackOn]; split_ifs <;> first | rfl | omega)
  rw [eZ, eH, eB] at h
  exact h.symm

/-! ## The core -/

/-- (354) on the top wire, every other control black. -/
theorem merge_top_core (b : Bool) :
    Derivable (theory (m + 4)) (drawn [Zc m (some b), Zc m (some !b)]) (Zc m none) := by
  have e1 : Derivable (theory (m + 4)) (drawn [Zc m (some b), Zc m (some !b)])
      (drawn [Hc m (some b), Bc m (some b), Hc m (some b), Bc m (some b),
        Hc m (some !b), Bc m (some !b), Hc m (some !b), Bc m (some !b)]) := by
    have h := dmul (exp333 ih (!b)) (exp333 ih b)
    rw [← drawn_two', ← SE.drawn_append] at h
    exact h
  have cBH' := comm_BH ih b
  have cHH' := comm_HH ih b (!b)
  have cBB' := comm_BB ih b (!b)
  have cHB' := comm_HB ih b
  set H := Hc m (some b)
  set B := Bc m (some b)
  set H' := Hc m (some !b)
  set B' := Bc m (some !b)
  set Hi := Hc m none
  set Bi := Bc m none
  have mH : Derivable (theory (m + 4)) (drawn [H, H']) (drawn [Hi]) := by
    rw [drawn_one']; exact merge_HH ih b
  have mB : Derivable (theory (m + 4)) (drawn [B, B']) (drawn [Bi]) := by
    rw [drawn_one']; exact merge_BB ih b
  -- `[H B H B H' B' H' B']` → `[H H' B B' H H' B B']` → `[Hi Bi Hi Bi]`
  have s1 : Derivable (theory (m + 4)) (drawn [H, B, H, B, H', B', H', B'])
      (drawn [H, B, H, H', B, B', H', B']) := sw_at [H, B, H] [B', H', B'] cBH'
  have s2 : Derivable (theory (m + 4)) (drawn [H, B, H, H', B, B', H', B'])
      (drawn [H, B, H', H, B, B', H', B']) := sw_at [H, B] [B, B', H', B'] cHH'
  have s3 : Derivable (theory (m + 4)) (drawn [H, B, H', H, B, B', H', B'])
      (drawn [H, H', B, H, B, B', H', B']) := sw_at [H] [H, B, B', H', B'] cBH'
  have s4 : Derivable (theory (m + 4)) (drawn [H, H', B, H, B, B', H', B'])
      (drawn [H, H', B, H, B', B, H', B']) := sw_at [H, H', B, H] [H', B'] cBB'
  have s5 : Derivable (theory (m + 4)) (drawn [H, H', B, H, B', B, H', B'])
      (drawn [H, H', B, B', H, B, H', B']) := sw_at [H, H', B] [B, H', B'] cHB'
  have s6 : Derivable (theory (m + 4)) (drawn [H, H', B, B', H, B, H', B'])
      (drawn [H, H', B, B', H, H', B, B']) := sw_at [H, H', B, B', H] [B'] cBH'
  have m1 : Derivable (theory (m + 4)) (drawn [H, H', B, B', H, H', B, B'])
      (drawn [Hi, B, B', H, H', B, B']) := rw_at [] [B, B', H, H', B, B'] mH
  have m2 : Derivable (theory (m + 4)) (drawn [Hi, B, B', H, H', B, B'])
      (drawn [Hi, Bi, H, H', B, B']) := rw_at [Hi] [H, H', B, B'] mB
  have m3 : Derivable (theory (m + 4)) (drawn [Hi, Bi, H, H', B, B'])
      (drawn [Hi, Bi, Hi, B, B']) := rw_at [Hi, Bi] [B, B'] mH
  have m4 : Derivable (theory (m + 4)) (drawn [Hi, Bi, Hi, B, B'])
      (drawn [Hi, Bi, Hi, Bi]) := rw_at [Hi, Bi, Hi] [] mB
  exact e1.trans (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (m1.trans
    (m2.trans (m3.trans (m4.trans (exp333_idle ih)))))))))))

end Core

end QCert.RealCliffordCH.Sec8.D.N15

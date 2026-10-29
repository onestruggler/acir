/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5, rule (45): the equations of Appendix D at any wires

The proof of rule (45) uses the commutation, merge and box-moving
equations of Appendix D on gates whose controls are full colourings of the
other wires.  `ctlF s tg` is such a colouring: the special wires `tg` idle,
every other wire `j` black where the bit `j` of `s` is `1`.  A frame `ps`
(the wires brought to the positions `0, 1, …`) carries the canonical gate
with the colouring `ctlP ps s tg` (the bits of `s` read through the frame)
to the gate on the wires `tg.map (frm ps)` coloured by `ctlF s`
(`frameF`), so each equation of the library, whose colours are free
parameters, holds at any wires (`commF`, `hgFrameF`, `move274F`,
`c308F`).
-/
import QCert.RealCliffordCH.Sec8.E.Rule43
import QCert.RealCliffordCH.Sec8.E.Rule22
import QCert.RealCliffordCH.Sec8.E.Step84
import QCert.RealCliffordCH.Sec8.E.MergeHg

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## Full colourings -/

/-- The special wires `tg` idle, the wire `j` black where the bit `j` of `s` is `1`. -/
def ctlF (s : ℕ) (tg : List ℕ) : ℕ → Option Bool :=
  fun j => if j ∈ tg then none else some (decide (bitOf s j = 1))

/-- The same, the bits read through the frame `ps`. -/
def ctlP (ps : List ℕ) (s : ℕ) (tg : List ℕ) : ℕ → Option Bool :=
  fun j => if j ∈ tg then none else some (decide (bitOf s (frm ps j) = 1))

/-- The colours of the frame `ps` on the canonical positions. -/
def pullF (ps : List ℕ) (s : ℕ) : ℕ → Bool := fun j => decide (bitOf s (frm ps j) = 1)

theorem ctlOf_F (s t : ℕ) : ctlOf s t = ctlF s [t] := by
  funext j; simp [ctlOf, ctlF]

theorem ctl2Of_F (s b h : ℕ) : ctl2Of s b h = ctlF s [b, h] := by
  funext j; simp [ctl2Of, ctlF]

theorem bitOf_hi45 {s j : ℕ} (hs : s < 16) (hj : 4 ≤ j) : bitOf s j = 0 :=
  bitOf_small (lt_of_lt_of_le hs (by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj))

section Frames

variable {N : ℕ}

theorem frm_mem_map {ps : List ℕ} (tg : List ℕ) (j : ℕ) :
    frm ps j ∈ tg.map (frm ps) ↔ j ∈ tg := by
  constructor
  · intro hm
    obtain ⟨u, hu, hue⟩ := List.mem_map.1 hm
    rw [← frm_injective ps hue]; exact hu
  · intro hm; exact List.mem_map.2 ⟨j, hm, rfl⟩

/-- A canonical gate coloured through the frame `ps`, its wires `I ⊇ tg` idle
or special, is the framed gate. -/
theorem frameFI (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (K : Kind) (tg I : List ℕ) (hl : tg.length = kindSp K) (htnd : tg.Nodup)
    (htN : ∀ t ∈ tg, t < N) (s : ℕ) :
    Derivable (theory N) (placedBy N (netOf ps) (mc N K tg (ctlP ps s I)))
      (mc N K (tg.map (frm ps)) (ctlF s (I.map (frm ps)))) := by
  have h := frame (mcSwapAll ih) hnd hps K tg (ctlF s (I.map (frm ps))) hl htnd htN
  have e : ctlF s (I.map (frm ps)) ∘ frm ps = ctlP ps s I := by
    funext j
    simp only [Function.comp, ctlF, ctlP]
    by_cases hj : j ∈ I
    · rw [if_pos hj, if_pos ((frm_mem_map I j).2 hj)]
    · rw [if_neg hj, if_neg (fun h => hj ((frm_mem_map I j).1 h))]
  rwa [e] at h

/-- `frameFI` with the special wires the only idle ones. -/
theorem frameF (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (K : Kind) (tg : List ℕ) (hl : tg.length = kindSp K) (htnd : tg.Nodup)
    (htN : ∀ t ∈ tg, t < N) (s : ℕ) :
    Derivable (theory N) (placedBy N (netOf ps) (mc N K tg (ctlP ps s tg)))
      (mc N K (tg.map (frm ps)) (ctlF s (tg.map (frm ps)))) :=
  frameFI ih hnd hps K tg tg hl htnd htN s

/-- `P ⊗ P` on the canonical wires `0, 1`, framed. -/
theorem framePP {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) (hN : 2 ≤ N) :
    Derivable (theory N) (placedBy N (netOf ps) (ppAt N 0 1)) (ppAt N (frm ps 0) (frm ps 1)) :=
  placeG_net (pp : Circ 2) (ps := [0, 1]) (by simp) (by intro p hp; simp at hp; omega) rfl
    (netOf ps) (netOf_ok hnd hps)

/-- Two colourings that differ on a wire off the frame differ on the canonical
positions after the frame. -/
theorem diffF {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {s s' w : ℕ}
    (hw : w < N) (hwp : w ∉ ps) (hb : bitOf s w ≠ bitOf s' w) :
    DiffOn ps.length N (pullF ps s) (pullF ps s') := by
  obtain ⟨h1, h2⟩ := D.N15.pos_ge hnd hps hw hwp
  refine ⟨pos (netOf ps) w, h1, h2, ?_⟩
  simp only [pullF, frm_pos]
  have := bitOf_lt_two s w; have := bitOf_lt_two s' w
  intro h
  apply hb
  by_cases e : bitOf s w = 1 <;> by_cases e' : bitOf s' w = 1 <;> simp_all <;> omega

/-- A commutation of canonical gates, framed. -/
theorem commF (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    {K₁ K₂ : Kind} {tg₁ tg₂ : List ℕ} (hl₁ : tg₁.length = kindSp K₁) (hl₂ : tg₂.length = kindSp K₂)
    (hn₁ : tg₁.Nodup) (hn₂ : tg₂.Nodup) (hN₁ : ∀ t ∈ tg₁, t < N) (hN₂ : ∀ t ∈ tg₂, t < N)
    {s₁ s₂ : ℕ} {c₁ c₂ : ℕ → Option Bool} (hc₁ : ∀ j < N, c₁ j = ctlP ps s₁ tg₁ j)
    (hc₂ : ∀ j < N, c₂ j = ctlP ps s₂ tg₂ j) (h : D.Comm N (mc N K₁ tg₁ c₁) (mc N K₂ tg₂ c₂)) :
    D.Comm N (mc N K₁ (tg₁.map (frm ps)) (ctlF s₁ (tg₁.map (frm ps))))
      (mc N K₂ (tg₂.map (frm ps)) (ctlF s₂ (tg₂.map (frm ps)))) := by
  rw [Net.mc_congr N K₁ tg₁ hc₁, Net.mc_congr N K₂ tg₂ hc₂] at h
  exact D.N15.comm_frame hnd hps (frameF ih hnd hps K₁ tg₁ hl₁ hn₁ hN₁ s₁)
    (frameF ih hnd hps K₂ tg₂ hl₂ hn₂ hN₂ s₂) h

end Frames

/-! ## The library equations at any wires -/

section Library

variable {N : ℕ}

/-- Pointwise equalities of control assignments on canonical positions. -/
macro "ctlP_tac" : tactic => `(tactic| (intro j hj; rcases j with _ | _ | _ | j <;>
  simp [ctlP, ctlOr, ctlAt, colOn, pullF, D.N13.hgCol, hj]))

/-- (337) at any wires: the box on `ps[0]` and the multi-controlled `H` with its
box on `ps[0]` and its `H` on `ps[1]`, separated on a wire `w`. -/
theorem comm337F (hN : 3 ≤ N) (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (hl : ps.length = 2) {s s' w : ℕ} (hw : w < N) (hwp : w ∉ ps) (hb : bitOf s w ≠ bitOf s' w) :
    D.Comm N (mc N .box ([0].map (frm ps)) (ctlF s ([0].map (frm ps))))
      (mc N .hg ([0, 1].map (frm ps)) (ctlF s' ([0, 1].map (frm ps)))) := by
  have hd := diffF hnd hps hw hwp hb
  rw [hl] at hd
  exact commF ih hnd hps rfl rfl (by simp) (by simp) (by simp; omega) (by simp; omega)
    (c₁ := ctlOr (ctlAt 1 (pullF ps s 1)) (colOn 2 N (pullF ps s)))
    (c₂ := colOn 2 N (pullF ps s')) (by ctlP_tac) (by ctlP_tac)
    (D.eq337 N hN ih _ _ hd _)

/-- (338) at any wires: the box on `ps[0]` and the multi-controlled `H` with its
`H` on `ps[0]` and its box on `ps[1]`. -/
theorem comm338F (hN : 3 ≤ N) (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (hl : ps.length = 2) (s s' : ℕ) :
    D.Comm N (mc N .box ([0].map (frm ps)) (ctlF s ([0].map (frm ps))))
      (mc N .hg ([1, 0].map (frm ps)) (ctlF s' ([1, 0].map (frm ps)))) :=
  commF ih hnd hps rfl rfl (by simp) (by simp) (by simp; omega) (by simp; omega)
    (c₁ := ctlOr (ctlAt 1 (pullF ps s 1)) (colOn 2 N (pullF ps s)))
    (c₂ := colOn 2 N (pullF ps s')) (by ctlP_tac) (by ctlP_tac)
    (D.eq338 N hN ih _ _ _)

/-- (340) at any wires. -/
theorem comm340F (hN : 3 ≤ N) (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (hl : ps.length = 2) (s s' : ℕ) :
    D.Comm N (mc N .hg ([0, 1].map (frm ps)) (ctlF s ([0, 1].map (frm ps))))
      (mc N .hg ([0, 1].map (frm ps)) (ctlF s' ([0, 1].map (frm ps)))) :=
  commF ih hnd hps rfl rfl (by simp) (by simp) (by simp; omega) (by simp; omega)
    (c₁ := colOn 2 N (pullF ps s)) (c₂ := colOn 2 N (pullF ps s')) (by ctlP_tac) (by ctlP_tac)
    (D.eq340 N hN ih _ _)

/-- (339) at any wires: the box on `ps[0]` and the multi-controlled `H` with its
box on `ps[1]` and its `H` on `ps[2]`, separated on a wire `w`. -/
theorem comm339F (hN : 4 ≤ N) (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (hl : ps.length = 3) {s s' w : ℕ} (hw : w < N) (hwp : w ∉ ps) (hb : bitOf s w ≠ bitOf s' w) :
    D.Comm N (mc N .box ([0].map (frm ps)) (ctlF s ([0].map (frm ps))))
      (mc N .hg ([1, 2].map (frm ps)) (ctlF s' ([1, 2].map (frm ps)))) := by
  have hd := diffF hnd hps hw hwp hb
  rw [hl] at hd
  exact commF ih hnd hps rfl rfl (by simp) (by simp) (by simp; omega) (by simp; omega)
    (c₁ := ctlOr (ctlAt 2 (pullF ps s 2)) (ctlOr (ctlAt 1 (pullF ps s 1)) (colOn 3 N (pullF ps s))))
    (c₂ := ctlOr (ctlAt 0 (pullF ps s' 0)) (colOn 3 N (pullF ps s'))) (by ctlP_tac) (by ctlP_tac)
    (D.eq339 N hN ih _ _ hd _ _ _)

/-- (344) at any wires: the multi-controlled `H` on `ps[0], ps[1]` and the one on
`ps[1], ps[2]`, separated on a wire `w`. -/
theorem comm344F (hN : 4 ≤ N) (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (hl : ps.length = 3) {s s' w : ℕ} (hw : w < N) (hwp : w ∉ ps) (hb : bitOf s w ≠ bitOf s' w) :
    D.Comm N (mc N .hg ([0, 1].map (frm ps)) (ctlF s ([0, 1].map (frm ps))))
      (mc N .hg ([1, 2].map (frm ps)) (ctlF s' ([1, 2].map (frm ps)))) := by
  have hd := diffF hnd hps hw hwp hb
  rw [hl] at hd
  exact commF ih hnd hps rfl rfl (by simp) (by simp) (by simp; omega) (by simp; omega)
    (c₁ := ctlOr (ctlAt 2 (pullF ps s 2)) (colOn 3 N (pullF ps s)))
    (c₂ := ctlOr (ctlAt 0 (pullF ps s' 0)) (colOn 3 N (pullF ps s'))) (by ctlP_tac) (by ctlP_tac)
    (D.eq344 N hN ih _ _ hd _ _)

/-- (312) at any wires. -/
theorem hgInvF (hN : 3 ≤ N) (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (hl : ps.length = 2) (s : ℕ) :
    Derivable (theory N) (mc N .hg ([0, 1].map (frm ps)) (ctlF s ([0, 1].map (frm ps))) *
      mc N .hg ([0, 1].map (frm ps)) (ctlF s ([0, 1].map (frm ps)))) 1 := by
  have f := frameF ih hnd hps .hg [0, 1] rfl (by simp) (by simp; omega) s
  have h := D.eq312 N hN ih (pullF ps s)
  rw [Net.mc_congr N .hg [0, 1] (c' := ctlP ps s [0, 1]) (by ctlP_tac)] at h
  have := via_frame hnd hps (L := [mc N .hg ([0, 1].map (frm ps)) (ctlF s ([0, 1].map (frm ps))),
    mc N .hg ([0, 1].map (frm ps)) (ctlF s ([0, 1].map (frm ps)))]) (R := [])
    (List.Forall₂.cons f (List.Forall₂.cons f List.Forall₂.nil)) List.Forall₂.nil h
  simpa [drawn] using this

/-- Definition 2.4 at the canonical wires, coloured, from four wires on. -/
theorem hgBoxN (hN : 4 ≤ N) (x : ℕ → Bool) :
    Derivable (theory N) (mc N .hg [0, 1] (colOn 2 N x))
      (ppAt N 0 1 * mc N .box [0] (colOn 1 N (D.N13.hgCol x)) * ppAt N 0 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 + 2 := ⟨N - 4, by omega⟩
  have h := D.N13.hg_box m x
  rw [D.N15.ppAt_eq (m + 2), mul_assoc]
  exact h

/-- Definition 2.4 at any wires: the multi-controlled `H` with box `ps[0]` and `H`
on `ps[1]` is the box on `ps[0]`, black on `ps[1]`, between two `P ⊗ P`. -/
theorem hgFrameF (hN : 4 ≤ N) (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (hl : 2 ≤ ps.length) (s s₂ : ℕ) (hs1 : bitOf s₂ (frm ps 1) = 1)
    (hs : ∀ j, j ≠ frm ps 1 → bitOf s₂ j = bitOf s j) :
    Derivable (theory N) (mc N .hg ([0, 1].map (frm ps)) (ctlF s ([0, 1].map (frm ps))))
      (ppAt N (frm ps 0) (frm ps 1) * mc N .box ([0].map (frm ps)) (ctlF s₂ ([0].map (frm ps))) *
        ppAt N (frm ps 0) (frm ps 1)) := by
  have h := hgBoxN hN (pullF ps s)
  rw [Net.mc_congr N .hg [0, 1] (c' := ctlP ps s [0, 1]) (by ctlP_tac),
    Net.mc_congr N .box [0] (c' := ctlP ps s₂ [0]) ?_] at h
  · have fH := frameF ih hnd hps .hg [0, 1] rfl (by simp) (by simp; omega) s
    have fB := frameF ih hnd hps .box [0] rfl (by simp) (by simp; omega) s₂
    have fP := framePP hnd hps (by omega)
    have := via_frame hnd hps (l := [mc N .hg [0, 1] (ctlP ps s [0, 1])])
      (r := [ppAt N 0 1, mc N .box [0] (ctlP ps s₂ [0]), ppAt N 0 1])
      (L := [mc N .hg ([0, 1].map (frm ps)) (ctlF s ([0, 1].map (frm ps)))])
      (R := [ppAt N (frm ps 0) (frm ps 1), mc N .box ([0].map (frm ps)) (ctlF s₂ ([0].map (frm ps))),
        ppAt N (frm ps 0) (frm ps 1)])
      (List.Forall₂.cons fH List.Forall₂.nil)
      (List.Forall₂.cons fP (List.Forall₂.cons fB (List.Forall₂.cons fP List.Forall₂.nil)))
      (by rw [D.N15.drawn_one', D.N15.drawn_three']; exact h)
    rwa [D.N15.drawn_one', D.N15.drawn_three'] at this
  · intro j hj
    rcases j with _ | _ | j
    · simp [colOn, ctlP]
    · simp [colOn, ctlP, D.N13.hgCol, hs1, show 1 < N by omega]
    · have hne : frm ps (j + 2) ≠ frm ps 1 := fun e => by have := frm_injective ps e; omega
      simp [colOn, ctlP, D.N13.hgCol, pullF, hs _ hne, hj]

/-- (308) at the canonical wires, coloured: `P ⊗ P` on the wires `0, 1` passes the
box on wire `1` with wire `0` idle. -/
theorem c308 (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) :
    D.Comm N (ppAt N 0 1) (mc N .box [1] (colOn 2 N x)) := by
  have h : D.Comm N (ppAt N 0 1) (mc N .box [1] (blackOn 2 N)) := by
    have := D.eq308 N hN ih 2 (by omega) (by omega) (pp : Circ 2)
    rwa [D.N8.atBot_pp N 0 (by omega)] at this
  obtain ⟨W, hW⟩ : ∃ W, W = (List.range N).filter (fun j => 2 ≤ j && !x j) := ⟨_, rfl⟩
  have hnd : W.Nodup := hW ▸ (List.nodup_range).filter _
  have hmem : ∀ j, j ∈ W ↔ 2 ≤ j ∧ j < N ∧ x j = false := by
    intro j; rw [hW]; simp only [List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_true']; tauto
  have hcol := colr43 (N := N) W hnd .box [1] (blackOn 2 N) (colOn 2 N x)
    (fun j hj => by
      obtain ⟨h1, h2, -⟩ := (hmem j).1 hj
      exact ⟨h2, by simp; omega, by simp [blackOn, h1, h2]⟩)
    (fun j hj => by
      by_cases hjw : j ∈ W
      · obtain ⟨h1, h2, h3⟩ := (hmem j).1 hjw
        rw [if_pos hjw]; simp [colOn, h1, h2, h3]
      · rw [if_neg hjw]
        by_cases h2 : 2 ≤ j
        · have : x j = true := by
            by_contra hx; exact hjw ((hmem j).2 ⟨h2, hj, by simpa using hx⟩)
          simp [colOn, blackOn, h2, hj, this]
        · simp [colOn, blackOn, h2])
  have hU : Derivable (theory N) (drawn (W.map (xAt N)) * drawn (W.map (xAt N))) 1 :=
    D.xs_inv N W hnd (fun w hw => ((hmem w).1 hw).2.1)
  have hUP : Derivable (theory N) (drawn (W.map (xAt N)) * ppAt N 0 1)
      (ppAt N 0 1 * drawn (W.map (xAt N))) :=
    D.N8.pp_comm (by omega) (D.N8.highW_xs N W (fun j hj => ((hmem j).1 hj).1))
  have hPU := D.N15.conj_of_comm (a := ppAt N 0 1) hU
    (by unfold D.Comm; rw [D.N13.drawn_two, D.N13.drawn_two]; exact hUP)
  exact D.N13.Comm.congr hPU hcol (D.N13.Comm.conj h hU)

/-- (308) at any wires: `P ⊗ P` on `ps[0], ps[1]` passes the box on `ps[1]` with
`ps[0]` idle. -/
theorem c308F (hN : 3 ≤ N) (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (hl : ps.length = 2) (s : ℕ) :
    D.Comm N (ppAt N (frm ps 0) (frm ps 1))
      (mc N .box ([1].map (frm ps)) (ctlF s ([0, 1].map (frm ps)))) := by
  have h := c308 hN ih (pullF ps s)
  rw [Net.mc_congr N .box [1] (c' := ctlP ps s [0, 1]) (by ctlP_tac)] at h
  exact D.N15.comm_frame hnd hps (framePP hnd hps (by omega))
    (frameFI ih hnd hps .box [1] [0, 1] rfl (by simp) (by simp; omega) s) h

/-- (274) at any wires: the box with `ps[0]`, `ps[1]` idle moves its box wire. -/
theorem move274F (hN : 3 ≤ N) (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (hl : ps.length = 2) (s : ℕ) :
    Derivable (theory N) (mc N .box ([0].map (frm ps)) (ctlF s ([0, 1].map (frm ps))))
      (mc N .box ([1].map (frm ps)) (ctlF s ([0, 1].map (frm ps)))) := by
  have h := move274 (pullF ps s) ih hN
  rw [Net.mc_congr N .box [0] (c' := ctlP ps s [0, 1]) (by ctlP_tac),
    Net.mc_congr N .box [1] (c' := ctlP ps s [0, 1]) (by ctlP_tac)] at h
  have f0 := frameFI ih hnd hps .box [0] [0, 1] rfl (by simp) (by simp; omega) s
  have f1 := frameFI ih hnd hps .box [1] [0, 1] rfl (by simp) (by simp; omega) s
  have := via_frame hnd hps (l := [mc N .box [0] (ctlP ps s [0, 1])])
    (r := [mc N .box [1] (ctlP ps s [0, 1])])
    (L := [mc N .box ([0].map (frm ps)) (ctlF s ([0, 1].map (frm ps)))])
    (R := [mc N .box ([1].map (frm ps)) (ctlF s ([0, 1].map (frm ps)))])
    (List.Forall₂.cons f0 List.Forall₂.nil) (List.Forall₂.cons f1 List.Forall₂.nil)
    (by rw [D.N15.drawn_one', D.N15.drawn_one']; exact h)
  rwa [D.N15.drawn_one', D.N15.drawn_one'] at this

/-- `P ⊗ P` is symmetric (Lemma 5.1 on three wires). -/
theorem ppSymm12 (hN : 4 ≤ N) (ih : IH N) :
    Derivable (theory N) (ppAt N 1 2) (ppAt N 2 1) := by
  have h3 : Derivable (theory 3) (placeG 3 (pp : Circ 2) [1, 2]) (placeG 3 (pp : Circ 2) [2, 1]) :=
    ih 3 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))
  have := der_atBot h3 N (by omega)
  rwa [atBot_placeG (pp : Circ 2) (k := 3) (qs := [1, 2]) (by decide) (by decide) rfl N (by omega),
    atBot_placeG (pp : Circ 2) (k := 3) (qs := [2, 1]) (by decide) (by decide) rfl N (by omega)] at this

end Library

end QCert.RealCliffordCH.Sec8.E

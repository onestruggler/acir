/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5, rule (45): the gates and the facts

On `N = M + 3 ≥ 4` wires, every gate of the proof of rule (45) has the local
wires `0, 1, 2, 3` and the wires `4, …` white controls; `ctlF s l` gives its
controls (the wires `l` idle or special, the local wire `j` black where the
bit `j` of `s` is `1`).  In the notation of `Core45Alg.alg45` (`H[b,t]` the
multi-controlled `H` with box `b` and `H` on `t`, `B[t]` the box on `t`):

* `a = H[2,0](1○ 3○)`, `b = H[0,1](2○ 3○)`, `w = B[0](1○ 2○ 3○)` (the decoded
  rule), `k = B[0](1○ 2● 3○)`, `f = H[0,1](2○ 3●)`;
* `v = B[0](1○ 3○)`, `e = H[0,1](2○)`, `β = B[0](1● 2○ 3○)`,
  `φ = B[0](1● 2○ 3●)`, `z' = B[0](1● 2○)`, `z = B[3](1● 2○)`,
  `z₀ = B[3](0○ 1● 2○)`, `z₁ = B[3](0● 1● 2○)`;
* `y = B[2](0● 1○ 3○)`, `y₀ = B[2](0○ 1○ 3○)`, `u₀ = B[2](0○ 1● 3○)`,
  `u₁ = B[2](0● 1● 3○)`, `v' = B[2](1○ 3○)`, `p = B[2](0○ 3○)`, `q = B[2](0● 3○)`;
* `h₀ = H[2,1](0○ 3○)`, `h₁ = H[2,1](0● 3○)`; `P₀₁`, `P₂₀`, `P₂₁` the `P ⊗ P`.

Each fact is an equation of Appendix D at these wires (`Core45Kit`); every
one was checked numerically at `N = 4, 5, 6` (`gen/sec8/e/m45b.py`).
-/
import QCert.RealCliffordCH.Sec8.E.Core45Kit

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## Colourings -/

theorem ctlF_ext {s s' : ℕ} {l l' : List ℕ}
    (h : ∀ j, (j ∈ l ↔ j ∈ l') ∧ (j ∉ l → bitOf s j = bitOf s' j)) : ctlF s l = ctlF s' l' := by
  funext j
  obtain ⟨h1, h2⟩ := h j
  simp only [ctlF]
  by_cases hj : j ∈ l
  · rw [if_pos hj, if_pos (h1.1 hj)]
  · rw [if_neg hj, if_neg (fun h => hj (h1.2 h)), h2 hj]

/-- Two colourings of the local wires `0, …, 3`, compared there. -/
theorem ctlF16 {s s' : ℕ} {l l' : List ℕ} (hs : s < 16) (hs' : s' < 16) (hl : ∀ j ∈ l, j < 4)
    (hl' : ∀ j ∈ l', j < 4) (h : ∀ j < 4, (j ∈ l ↔ j ∈ l') ∧ (j ∉ l → bitOf s j = bitOf s' j)) :
    ctlF s l = ctlF s' l' := by
  refine ctlF_ext fun j => ?_
  by_cases hj : j < 4
  · exact h j hj
  · refine ⟨⟨fun hm => absurd (hl j hm) hj, fun hm => absurd (hl' j hm) hj⟩, fun _ => ?_⟩
    rw [bitOf_hi45 hs (by omega), bitOf_hi45 hs' (by omega)]

theorem bits16 {s s' w : ℕ} (hs : s < 16) (hs' : s' < 16)
    (h : ∀ j < 4, j ≠ w → bitOf s' j = bitOf s j) : ∀ j, j ≠ w → bitOf s' j = bitOf s j := by
  intro j hj
  by_cases h4 : j < 4
  · exact h j h4 hj
  · rw [bitOf_hi45 hs' (by omega), bitOf_hi45 hs (by omega)]

theorem setCtl_noneF (s : ℕ) (l : List ℕ) (w : ℕ) : setCtl (ctlF s l) w none = ctlF s (w :: l) := by
  funext j
  simp only [setCtl, ctlF, List.mem_cons]
  by_cases hj : j = w <;> simp [hj]

theorem setCtl_someF {s s' : ℕ} {l : List ℕ} {w : ℕ} {b : Bool} (hs : s < 16) (hs' : s' < 16)
    (hw : w ∉ l) (hb : decide (bitOf s' w = 1) = b)
    (h : ∀ j < 4, j ≠ w → j ∉ l → bitOf s' j = bitOf s j) :
    setCtl (ctlF s l) w (some b) = ctlF s' l := by
  funext j
  simp only [setCtl, ctlF]
  by_cases hj : j = w
  · subst hj; simp [hw, hb]
  · rw [if_neg hj]
    by_cases hjl : j ∈ l
    · simp [hjl]
    · have hb' : bitOf s' j = bitOf s j := by
        by_cases h4 : j < 4
        · exact h j h4 hj hjl
        · rw [bitOf_hi45 hs' (by omega), bitOf_hi45 hs (by omega)]
      simp [hjl, hb']

/-! ## The gates -/

section Gates

variable (M : ℕ)

abbrev gA45 : Circ (M + 3) := mc (M + 3) .hg [2, 0] (ctlF 0 [2, 0])
abbrev gB45 : Circ (M + 3) := mc (M + 3) .hg [0, 1] (ctlF 0 [0, 1])
abbrev gW45 : Circ (M + 3) := mc (M + 3) .box [0] (ctlF 0 [0])
abbrev gK45 : Circ (M + 3) := mc (M + 3) .box [0] (ctlF 4 [0])
abbrev gF45 : Circ (M + 3) := mc (M + 3) .hg [0, 1] (ctlF 8 [0, 1])
abbrev gV45 : Circ (M + 3) := mc (M + 3) .box [0] (ctlF 0 [2, 0])
abbrev gE45 : Circ (M + 3) := mc (M + 3) .hg [0, 1] (ctlF 0 [3, 0, 1])
abbrev gBe45 : Circ (M + 3) := mc (M + 3) .box [0] (ctlF 2 [0])
abbrev gPh45 : Circ (M + 3) := mc (M + 3) .box [0] (ctlF 10 [0])
abbrev gZp45 : Circ (M + 3) := mc (M + 3) .box [0] (ctlF 2 [3, 0])
abbrev gZ45 : Circ (M + 3) := mc (M + 3) .box [3] (ctlF 2 [3, 0])
abbrev gZ045 : Circ (M + 3) := mc (M + 3) .box [3] (ctlF 2 [3])
abbrev gZ145 : Circ (M + 3) := mc (M + 3) .box [3] (ctlF 3 [3])
abbrev gY45 : Circ (M + 3) := mc (M + 3) .box [2] (ctlF 1 [2])
abbrev gY045 : Circ (M + 3) := mc (M + 3) .box [2] (ctlF 0 [2])
abbrev gU045 : Circ (M + 3) := mc (M + 3) .box [2] (ctlF 2 [2])
abbrev gU145 : Circ (M + 3) := mc (M + 3) .box [2] (ctlF 3 [2])
abbrev gVp45 : Circ (M + 3) := mc (M + 3) .box [2] (ctlF 0 [2, 0])
abbrev gP45 : Circ (M + 3) := mc (M + 3) .box [2] (ctlF 0 [1, 2])
abbrev gQ45 : Circ (M + 3) := mc (M + 3) .box [2] (ctlF 1 [1, 2])
abbrev gH045 : Circ (M + 3) := mc (M + 3) .hg [2, 1] (ctlF 0 [2, 1])
abbrev gH145 : Circ (M + 3) := mc (M + 3) .hg [2, 1] (ctlF 1 [2, 1])
abbrev gP0145 : Circ (M + 3) := ppAt (M + 3) 0 1
abbrev gP2045 : Circ (M + 3) := ppAt (M + 3) 2 0
abbrev gP2145 : Circ (M + 3) := ppAt (M + 3) 2 1

end Gates

/-! ## The facts -/

section Facts

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- A box on wire `t` is an involution. -/
theorem i45box {t : ℕ} (ht : t < M + 3) (s : ℕ) :
    Derivable (theory (M + 3))
      (mc (M + 3) .box [t] (ctlF s [t]) * mc (M + 3) .box [t] (ctlF s [t])) 1 := by
  have := box_inv ih (t := t) (s := s) ht
  rwa [D.N13.drawn_two, ctlOf_F] at this

/-- A multi-controlled `H` is an involution. -/
theorem i45hg {b h : ℕ} (hb : b < M + 3) (hh : h < M + 3) (hbh : b ≠ h) (s : ℕ) :
    Derivable (theory (M + 3))
      (mc (M + 3) .hg [b, h] (ctlF s [b, h]) * mc (M + 3) .hg [b, h] (ctlF s [b, h])) 1 := by
  have hnd : [b, h].Nodup := by simp [hbh]
  have hps : ∀ p ∈ [b, h], p < M + 3 := by simp [hb, hh]
  have f0 : frm [b, h] 0 = b := frm_getD hnd hps (by simp)
  have f1 : frm [b, h] 1 = h := frm_getD hnd hps (by simp)
  have := hgInvF (by omega) ih hnd hps rfl s
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

/-- Two boxes commute. -/
theorem c45box {t t' : ℕ} (ht : t < M + 3) (ht' : t' < M + 3) (s s' : ℕ) :
    D.Comm (M + 3) (mc (M + 3) .box [t] (ctlF s [t])) (mc (M + 3) .box [t'] (ctlF s' [t'])) := by
  have := boxes_comm ih (s := s) (s' := s') ht ht'
  simpa only [ctlOf_F] using this

/-- (309) on the box `t` over the wire `w`. -/
theorem m45box {t w : ℕ} (ht : t < M + 3) (hw : w < M + 3) (hwt : w ≠ t) (l : List ℕ)
    (htl : t ∈ l) (hwl : w ∉ l) (s s₀ s₁ : ℕ) (hs : s < 16) (hs₀ : s₀ < 16) (hs₁ : s₁ < 16)
    (h₀ : decide (bitOf s₀ w = 1) = false) (h₁ : decide (bitOf s₁ w = 1) = true)
    (hb₀ : ∀ j < 4, j ≠ w → j ∉ l → bitOf s₀ j = bitOf s j)
    (hb₁ : ∀ j < 4, j ≠ w → j ∉ l → bitOf s₁ j = bitOf s j) :
    Derivable (theory (M + 3)) (mc (M + 3) .box [t] (ctlF s₁ l) * mc (M + 3) .box [t] (ctlF s₀ l))
      (mc (M + 3) .box [t] (ctlF s (w :: l))) := by
  have h := mergeAt ih ht (ctlF s l) (by simp [ctlF, htl]) hwt hw false
  rw [D.N13.drawn_two, setCtl_noneF, Bool.not_false, setCtl_someF hs hs₀ hwl h₀ hb₀,
    setCtl_someF hs hs₁ hwl h₁ hb₁] at h
  exact h

/-! ### The box `k` and the gate `f` -/

theorem f45kb : D.Comm (M + 3) (gK45 M) (gB45 M) := by
  have hnd : [0, 1].Nodup := by decide
  have hps : ∀ p ∈ [0, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [0, 1] 0 = 0 := frm_getD hnd hps (by simp)
  have f1 : frm [0, 1] 1 = 1 := frm_getD hnd hps (by simp)
  have := comm337F (by omega) ih hnd hps rfl (s := 4) (s' := 0) (w := 2) (by omega) (by decide)
    (by decide)
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

theorem f45kf : D.Comm (M + 3) (gK45 M) (gF45 M) := by
  have hnd : [0, 1].Nodup := by decide
  have hps : ∀ p ∈ [0, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [0, 1] 0 = 0 := frm_getD hnd hps (by simp)
  have f1 : frm [0, 1] 1 = 1 := frm_getD hnd hps (by simp)
  have := comm337F (by omega) ih hnd hps rfl (s := 4) (s' := 8) (w := 2) (by omega) (by decide)
    (by decide)
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

theorem f45wf (hM : 1 ≤ M) : D.Comm (M + 3) (gW45 M) (gF45 M) := by
  have hnd : [0, 1].Nodup := by decide
  have hps : ∀ p ∈ [0, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [0, 1] 0 = 0 := frm_getD hnd hps (by simp)
  have f1 : frm [0, 1] 1 = 1 := frm_getD hnd hps (by simp)
  have := comm337F (by omega) ih hnd hps rfl (s := 0) (s' := 8) (w := 3) (by omega) (by decide)
    (by decide)
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

theorem f45ka : D.Comm (M + 3) (gK45 M) (gA45 M) := by
  have hnd : [0, 2].Nodup := by decide
  have hps : ∀ p ∈ [0, 2], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [0, 2] 0 = 0 := frm_getD hnd hps (by simp)
  have f1 : frm [0, 2] 1 = 2 := frm_getD hnd hps (by simp)
  have := comm338F (by omega) ih hnd hps rfl 4 0
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

theorem f45af (hM : 1 ≤ M) : D.Comm (M + 3) (gA45 M) (gF45 M) := by
  have hnd : [2, 0, 1].Nodup := by decide
  have hps : ∀ p ∈ [2, 0, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [2, 0, 1] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 0, 1] 1 = 0 := frm_getD hnd hps (by simp)
  have f2 : frm [2, 0, 1] 2 = 1 := frm_getD hnd hps (by simp)
  have := comm344F (by omega) ih hnd hps rfl (s := 0) (s' := 8) (w := 3) (by omega) (by decide)
    (by decide)
  simpa only [List.map_cons, List.map_nil, f0, f1, f2] using this

theorem f45fb : D.Comm (M + 3) (gF45 M) (gB45 M) := by
  have hnd : [0, 1].Nodup := by decide
  have hps : ∀ p ∈ [0, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [0, 1] 0 = 0 := frm_getD hnd hps (by simp)
  have f1 : frm [0, 1] 1 = 1 := frm_getD hnd hps (by simp)
  have := comm340F (by omega) ih hnd hps rfl 8 0
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

/-- `w k = v` ((309) over wire `2`). -/
theorem f45v : Derivable (theory (M + 3)) (gK45 M * gW45 M) (gV45 M) :=
  m45box ih (t := 0) (w := 2) (by omega) (by omega) (by omega) [0] (by simp) (by simp) 0 0 4
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide)

/-- `b f = e` ((310) over wire `3`). -/
theorem f45e (hM : 1 ≤ M) : Derivable (theory (M + 3)) (gF45 M * gB45 M) (gE45 M) := by
  have h := mergeHgAt ih (bw := 0) (hw := 1) (by omega) (by omega) (by omega) (ctlF 0 [0, 1])
    (by simp [ctlF]) (by simp [ctlF]) (w := 3) (by omega) (by omega) (by omega) false
  rw [D.N13.drawn_two, setCtl_noneF, Bool.not_false,
    setCtl_someF (s' := 8) (b := true) (by norm_num) (by norm_num) (by simp) (by decide) (by decide),
    setCtl_someF (s' := 0) (b := false) (by norm_num) (by norm_num) (by simp) (by decide)
      (by decide)] at h
  exact h

/-! ### Definition 2.4, Klein, (308), merges and moves -/

theorem f45b (hM : 1 ≤ M) :
    Derivable (theory (M + 3)) (gB45 M) (gP0145 M * gBe45 M * gP0145 M) := by
  have hnd : [0, 1].Nodup := by decide
  have hps : ∀ p ∈ [0, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [0, 1] 0 = 0 := frm_getD hnd hps (by simp)
  have f1 : frm [0, 1] 1 = 1 := frm_getD hnd hps (by simp)
  have := hgFrameF (by omega) ih hnd hps (by simp) 0 2 (by rw [f1]; decide)
    (by rw [f1]; exact bits16 (by norm_num) (by norm_num) (by decide))
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

theorem f45f (hM : 1 ≤ M) :
    Derivable (theory (M + 3)) (gF45 M) (gP0145 M * gPh45 M * gP0145 M) := by
  have hnd : [0, 1].Nodup := by decide
  have hps : ∀ p ∈ [0, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [0, 1] 0 = 0 := frm_getD hnd hps (by simp)
  have f1 : frm [0, 1] 1 = 1 := frm_getD hnd hps (by simp)
  have := hgFrameF (by omega) ih hnd hps (by simp) 8 10 (by rw [f1]; decide)
    (by rw [f1]; exact bits16 (by norm_num) (by norm_num) (by decide))
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

/-- `β φ = z'` ((309) over wire `3`). -/
theorem f45zp (hM : 1 ≤ M) : Derivable (theory (M + 3)) (gPh45 M * gBe45 M) (gZp45 M) :=
  m45box ih (t := 0) (w := 3) (by omega) (by omega) (by omega) [0] (by simp) (by simp) 2 2 10
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide)

theorem f45a (hM : 1 ≤ M) :
    Derivable (theory (M + 3)) (gA45 M) (gP2045 M * gY45 M * gP2045 M) := by
  have hnd : [2, 0].Nodup := by decide
  have hps : ∀ p ∈ [2, 0], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [2, 0] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 0] 1 = 0 := frm_getD hnd hps (by simp)
  have := hgFrameF (by omega) ih hnd hps (by simp) 0 1 (by rw [f1]; decide)
    (by rw [f1]; exact bits16 (by norm_num) (by norm_num) (by decide))
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

theorem f45vP : D.Comm (M + 3) (gP2045 M) (gV45 M) := by
  have hnd : [2, 0].Nodup := by decide
  have hps : ∀ p ∈ [2, 0], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [2, 0] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 0] 1 = 0 := frm_getD hnd hps (by simp)
  have := c308F (by omega) ih hnd hps rfl 0
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

/-- `v = v'` ((274)). -/
theorem f45vv : Derivable (theory (M + 3)) (gV45 M) (gVp45 M) := by
  have hnd : [2, 0].Nodup := by decide
  have hps : ∀ p ∈ [2, 0], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [2, 0] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 0] 1 = 0 := frm_getD hnd hps (by simp)
  have := move274F (by omega) ih hnd hps rfl 0
  simp only [List.map_cons, List.map_nil, f0, f1] at this
  exact this.symm

/-- `y₀ y = v'` ((309) over wire `0`). -/
theorem f45vp : Derivable (theory (M + 3)) (gY45 M * gY045 M) (gVp45 M) := by
  have h := m45box ih (t := 2) (w := 0) (by omega) (by omega) (by omega) [2] (by simp) (by simp)
    0 0 1 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide)
  rwa [show ctlF 0 [0, 2] = ctlF 0 [2, 0] from
    ctlF16 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)] at h

/-- `y₀ u₀ = p` ((309) over wire `1`). -/
theorem f45p : Derivable (theory (M + 3)) (gU045 M * gY045 M) (gP45 M) :=
  m45box ih (t := 2) (w := 1) (by omega) (by omega) (by omega) [2] (by simp) (by simp) 0 0 2
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide)

/-- `y u₁ = q` ((309) over wire `1`). -/
theorem f45q : Derivable (theory (M + 3)) (gU145 M * gY45 M) (gQ45 M) :=
  m45box ih (t := 2) (w := 1) (by omega) (by omega) (by omega) [2] (by simp) (by simp) 1 1 3
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide)

theorem f45P12 (hM : 1 ≤ M) (s : ℕ) :
    D.Comm (M + 3) (gP2145 M) (mc (M + 3) .box [2] (ctlF s [1, 2])) := by
  have hnd : [1, 2].Nodup := by decide
  have hps : ∀ p ∈ [1, 2], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [1, 2] 0 = 1 := frm_getD hnd hps (by simp)
  have f1 : frm [1, 2] 1 = 2 := frm_getD hnd hps (by simp)
  have := c308F (by omega) ih hnd hps rfl s
  simp only [List.map_cons, List.map_nil, f0, f1] at this
  exact D.N13.Comm.congr (ppSymm12 (by omega) ih) (Derivable.refl _) this

theorem f45h0 (hM : 1 ≤ M) :
    Derivable (theory (M + 3)) (gH045 M) (gP2145 M * gU045 M * gP2145 M) := by
  have hnd : [2, 1].Nodup := by decide
  have hps : ∀ p ∈ [2, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [2, 1] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 1] 1 = 1 := frm_getD hnd hps (by simp)
  have := hgFrameF (by omega) ih hnd hps (by simp) 0 2 (by rw [f1]; decide)
    (by rw [f1]; exact bits16 (by norm_num) (by norm_num) (by decide))
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

theorem f45h1 (hM : 1 ≤ M) :
    Derivable (theory (M + 3)) (gH145 M) (gP2145 M * gU145 M * gP2145 M) := by
  have hnd : [2, 1].Nodup := by decide
  have hps : ∀ p ∈ [2, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [2, 1] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 1] 1 = 1 := frm_getD hnd hps (by simp)
  have := hgFrameF (by omega) ih hnd hps (by simp) 1 3 (by rw [f1]; decide)
    (by rw [f1]; exact bits16 (by norm_num) (by norm_num) (by decide))
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

/-- `z' = z` ((274)). -/
theorem f45zz (hM : 1 ≤ M) : Derivable (theory (M + 3)) (gZp45 M) (gZ45 M) := by
  have hnd : [3, 0].Nodup := by decide
  have hps : ∀ p ∈ [3, 0], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [3, 0] 0 = 3 := frm_getD hnd hps (by simp)
  have f1 : frm [3, 0] 1 = 0 := frm_getD hnd hps (by simp)
  have := move274F (by omega) ih hnd hps rfl 2
  simp only [List.map_cons, List.map_nil, f0, f1] at this
  exact this.symm

/-- `z₀ z₁ = z` ((309) over wire `0`). -/
theorem f45z (hM : 1 ≤ M) : Derivable (theory (M + 3)) (gZ145 M * gZ045 M) (gZ45 M) := by
  have h := m45box ih (t := 3) (w := 0) (by omega) (by omega) (by omega) [3] (by simp) (by simp)
    2 2 3 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide)
  rwa [show ctlF 2 [0, 3] = ctlF 2 [3, 0] from
    ctlF16 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)] at h

theorem f45z1h0 (hM : 1 ≤ M) : D.Comm (M + 3) (gZ145 M) (gH045 M) := by
  have hnd : [3, 2, 1].Nodup := by decide
  have hps : ∀ p ∈ [3, 2, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [3, 2, 1] 0 = 3 := frm_getD hnd hps (by simp)
  have f1 : frm [3, 2, 1] 1 = 2 := frm_getD hnd hps (by simp)
  have f2 : frm [3, 2, 1] 2 = 1 := frm_getD hnd hps (by simp)
  have := comm339F (by omega) ih hnd hps rfl (s := 3) (s' := 0) (w := 0) (by omega) (by decide)
    (by decide)
  simpa only [List.map_cons, List.map_nil, f0, f1, f2] using this

theorem f45z0h1 (hM : 1 ≤ M) : D.Comm (M + 3) (gZ045 M) (gH145 M) := by
  have hnd : [3, 2, 1].Nodup := by decide
  have hps : ∀ p ∈ [3, 2, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [3, 2, 1] 0 = 3 := frm_getD hnd hps (by simp)
  have f1 : frm [3, 2, 1] 1 = 2 := frm_getD hnd hps (by simp)
  have f2 : frm [3, 2, 1] 2 = 1 := frm_getD hnd hps (by simp)
  have := comm339F (by omega) ih hnd hps rfl (s := 2) (s' := 1) (w := 0) (by omega) (by decide)
    (by decide)
  simpa only [List.map_cons, List.map_nil, f0, f1, f2] using this

theorem f45h0h1 : D.Comm (M + 3) (gH045 M) (gH145 M) := by
  have hnd : [2, 1].Nodup := by decide
  have hps : ∀ p ∈ [2, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [2, 1] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 1] 1 = 1 := frm_getD hnd hps (by simp)
  have := comm340F (by omega) ih hnd hps rfl 0 1
  simpa only [List.map_cons, List.map_nil, f0, f1] using this

end Facts

end QCert.RealCliffordCH.Sec8.E

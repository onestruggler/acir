/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equations (347)–(352), from four wires on

The paper's argument (page 234): write every rotation as boxes and
multi-controlled `H` gates "with a hole" (`RotDec.dec_at`), and each pair
of factors is one of (335)–(345) (`Framed`).  The box wire `b` and the hole
`h` of each decomposition are chosen so that every pair is such an
instance; where a pair needs a separating control, `b` and `h` avoid the
wire `j` where the two colourings differ, which needs a wire to spare
besides `j`, hence four wires.  The choices (checked numerically,
`gen/sec8/n13/r347.py`):

* (347) target `1`, `b = 2`, `h = 0`: (337) and (336) — from three wires.
* (348) target `0`, `b = 1`, `h ∈ {2, 3} ∖ {j}`: (338) and (344).
* (349) target `1`, `h = 0`, `b ∈ {2, 3} ∖ {j}`: (340) and (339).
* (350) target `2`, `b = 0`, `h = 1`: (337) and (344).
* (351) both target `0`, the same `b ≠ h` in `{1, 2, 3} ∖ {j}`: (340),
  (335) and (339) twice; when the colourings agree, (317).
* (352) targets `0`, `1` with holes `1`, `0` and the same box wire
  `b ∈ {2, 3} ∖ {j}`: (345), (335) and (339) twice.

The decompositions with `b > h` use (353) (`S353`), through `E.McSwapAll`.
-/
import QCert.RealCliffordCH.Sec8.D.N13.Framed

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13.R347

open Circuit Net E Eng

/-- A control function with a control on every wire off `ps`. -/
macro "full_tac" : tactic => `(tactic| (
  intro i hi hni
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hni
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i) with h | h | h | h <;>
  first
  | (exfalso; omega)
  | (subst h; simp [setCtl, ctlOr, ctlAt, colOn, hni, hi]; done)
  | (simp [setCtl, ctlOr, ctlAt, colOn, hni, hi, show i ≠ 0 by omega, show i ≠ 1 by omega,
      show i ≠ 2 by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 1 ≤ i by omega]; done)))

theorem nd2 {a b : ℕ} (h : a ≠ b) : [a, b].Nodup := by simp [h]

theorem nd3 {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : [a, b, c].Nodup := by
  simp [hab, hac, hbc]

theorem lt2 {N a b : ℕ} (ha : a < N) (hb : b < N) : ∀ p ∈ [a, b], p < N := by simp [ha, hb]

theorem lt3 {N a b c : ℕ} (ha : a < N) (hb : b < N) (hc : c < N) : ∀ p ∈ [a, b, c], p < N := by
  simp [ha, hb, hc]

theorem mem_dw {N : ℕ} {a : Bool} {g b x : Circ N} (h : x ∈ dw a g b) : x = g ∨ x = b := by
  cases a <;> simp only [dw, Bool.false_eq_true, if_false, if_true, List.mem_cons,
    List.mem_nil_iff, or_false] at h <;> tauto

/-- A gate commuting with both factors commutes with the rotation they make. -/
theorem comm_dw {N : ℕ} {O g b : Circ N} (a : Bool) (hg : D.Comm N O g) (hb : D.Comm N O b) :
    D.Comm N O (drawn (dw a g b)) :=
  Derivable.symm (N13.comm_drawn_left _ (fun x hx => by
    rcases mem_dw hx with rfl | rfl
    · exact Derivable.symm hg
    · exact Derivable.symm hb))

/-- Two rotations whose factors commute pairwise. -/
theorem comm_dw2 {N : ℕ} {g b g' b' : Circ N} (a a' : Bool) (h1 : D.Comm N g g')
    (h2 : D.Comm N g b') (h3 : D.Comm N b g') (h4 : D.Comm N b b') :
    D.Comm N (drawn (dw a g b)) (drawn (dw a' g' b')) :=
  N13.comm_drawn _ _ (fun x hx y hy => by
    rcases mem_dw hx with rfl | rfl <;> rcases mem_dw hy with rfl | rfl <;> assumption)

/-! ## (347) -/

theorem comm347 {N : ℕ} (hN : 3 ≤ N) (ih : IH N) (hsw : E.McSwapAll N) (h333 : H333 N)
    (h334 : H334 N) (h336 : H336 N) (h337 : H337 N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a c₁ c₂ : Bool) :
    D.Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
      (mc N (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))) := by
  have hc : ∀ i < N, ctlOr (ctlAt 0 c₂) (colOn 2 N y) i = none ↔ i = 1 := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with h | h | h
    · subst h; simp [ctlOr, ctlAt]
    · subst h; simp [ctlOr, ctlAt, colOn]
    · simp [ctlOr, ctlAt, colOn, show i ≠ 0 by omega, show i ≠ 1 by omega, h, hi]
  have hd := dec_at hN ih hsw h333 h334 a (t := 1) (b := 2) (h := 0) (by omega) (by omega)
    (by omega) (by decide) (by decide) (by decide) _ hc
  refine Comm.congr (Derivable.refl _) hd.symm (comm_dw a ?_ ?_)
  · have e : mc N .hg [0, 1] (setCtl (ctlOr (ctlAt 0 c₂) (colOn 2 N y)) 0 none) =
        mc N .hg [0, 1] (colOn 2 N y) := Net.mc_congr _ _ _ (fun i hi => by
      by_cases h0 : i = 0
      · subst h0; simp [setCtl, colOn]
      · simp [setCtl, ctlOr, ctlAt, h0])
    rw [e]; exact h337 x y hxy c₁
  · exact f336 hN ih h336 (p₀ := 0) (p₁ := 2) (nd2 (by decide)) (lt2 (by omega) (by omega))
      (a₁ := x 2) (b₀ := c₂) (by simp [ctlOr, ctlAt, colOn])
      (by simp [ctlOr, ctlAt, colOn, show 2 < N by omega]) (by full_tac)
      (by simp [setCtl, ctlOr, ctlAt]) (by simp [setCtl]) (by full_tac)

/-! ## (348) -/

theorem comm348 {N : ℕ} (hN : 4 ≤ N) (ih : IH N) (hsw : E.McSwapAll N) (h333 : H333 N)
    (h334 : H334 N) (h338 : H338 N) (h344 : H344 N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a c₁ : Bool) :
    D.Comm N (mc N .hg [0, 1] (colOn 2 N x))
      (mc N (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N y))) := by
  obtain ⟨j, hj2, hjN, hxyj⟩ := hxy
  obtain ⟨h₀, hh2, hh3, hhj⟩ : ∃ h, 2 ≤ h ∧ h ≤ 3 ∧ h ≠ j :=
    ⟨if j = 2 then 3 else 2, by split_ifs <;> omega, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  have hc : ∀ i < N, ctlOr (ctlAt 1 c₁) (colOn 2 N y) i = none ↔ i = 0 := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with h | h | h
    · subst h; simp [ctlOr, ctlAt, colOn]
    · subst h; simp [ctlOr, ctlAt]
    · simp [ctlOr, ctlAt, colOn, show i ≠ 0 by omega, show i ≠ 1 by omega, h, hi]
  have hd := dec_at (by omega) ih hsw h333 h334 a (t := 0) (b := 1) (h := h₀) (by omega)
    (by omega) (by omega) (by decide) (by omega) (by omega) _ hc
  refine Comm.congr (Derivable.refl _) hd.symm (comm_dw a ?_ ?_)
  · -- (344) on the wires `h₀, 0, 1`
    refine Derivable.symm (f344 (by omega) ih h344 (p₀ := h₀) (p₁ := 0) (p₂ := 1)
      (nd3 (by omega) (by omega) (by decide)) (lt3 (by omega) (by omega) (by omega))
      (a₂ := c₁) (b₀ := x h₀) (by simp [setCtl]) (by simp [setCtl, ctlOr, ctlAt, colOn,
        show (0 : ℕ) ≠ h₀ by omega]) (by simp [setCtl, ctlOr, ctlAt, show (1 : ℕ) ≠ h₀ by omega])
      (by full_tac) (by simp [colOn, hh2, show h₀ < N by omega]) (by simp [colOn])
      (by simp [colOn]) (by full_tac) (j := j) (u := y j) (v := x j) hjN
      (by simp; omega) ?_ (by simp [colOn, hj2, hjN]) (Ne.symm hxyj))
    simp [setCtl, ctlOr, ctlAt, colOn, show j ≠ h₀ by omega, show j ≠ 1 by omega, hj2, hjN]
  · -- (338) on the wires `1, 0`
    exact Derivable.symm (f338 (by omega) ih h338 (p₀ := 1) (p₁ := 0) (nd2 (by decide))
      (lt2 (by omega) (by omega)) (a₁ := true) (by simp [setCtl]) (by simp [setCtl])
      (by full_tac) (by simp [colOn]) (by simp [colOn]) (by full_tac))

/-! ## (349) -/

theorem comm349 {N : ℕ} (hN : 4 ≤ N) (ih : IH N) (hsw : E.McSwapAll N) (h333 : H333 N)
    (h334 : H334 N) (h339 : H339 N) (h340 : H340 N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a c₁ : Bool) :
    D.Comm N (mc N .hg [0, 1] (colOn 2 N x))
      (mc N (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 c₁) (colOn 2 N y))) := by
  obtain ⟨j, hj2, hjN, hxyj⟩ := hxy
  obtain ⟨b₀, hb2, hb3, hbj⟩ : ∃ b, 2 ≤ b ∧ b ≤ 3 ∧ b ≠ j :=
    ⟨if j = 2 then 3 else 2, by split_ifs <;> omega, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  have hc : ∀ i < N, ctlOr (ctlAt 0 c₁) (colOn 2 N y) i = none ↔ i = 1 := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with h | h | h
    · subst h; simp [ctlOr, ctlAt]
    · subst h; simp [ctlOr, ctlAt, colOn]
    · simp [ctlOr, ctlAt, colOn, show i ≠ 0 by omega, show i ≠ 1 by omega, h, hi]
  have hd := dec_at (by omega) ih hsw h333 h334 a (t := 1) (b := b₀) (h := 0) (by omega)
    (by omega) (by omega) (by omega) (by decide) (by omega) _ hc
  refine Comm.congr (Derivable.refl _) hd.symm (comm_dw a ?_ ?_)
  · -- (340)
    have e : mc N .hg [0, 1] (setCtl (ctlOr (ctlAt 0 c₁) (colOn 2 N y)) 0 none) =
        mc N .hg [0, 1] (colOn 2 N y) := Net.mc_congr _ _ _ (fun i hi => by
      by_cases h0 : i = 0
      · subst h0; simp [setCtl, colOn]
      · simp [setCtl, ctlOr, ctlAt, h0])
    rw [e]; exact h340 x y
  · -- (339) on the wires `b₀, 0, 1`
    refine Derivable.symm (f339 (by omega) ih h339 (p₀ := b₀) (p₁ := 0) (p₂ := 1)
      (nd3 (by omega) (by omega) (by decide)) (lt3 (by omega) (by omega) (by omega))
      (a₁ := c₁) (a₂ := true) (h₀ := x b₀) (by simp [setCtl, show b₀ ≠ 1 by omega])
      (by simp [setCtl, ctlOr, ctlAt, show (0 : ℕ) ≠ b₀ by omega]) (by simp [setCtl])
      (by full_tac) (by simp [colOn, hb2, show b₀ < N by omega]) (by simp [colOn])
      (by simp [colOn]) (by full_tac) (j := j) (u := y j) (v := x j) hjN
      (by simp; omega) ?_ (by simp [colOn, hj2, hjN]) (Ne.symm hxyj))
    simp [setCtl, ctlOr, ctlAt, colOn, show j ≠ b₀ by omega, show j ≠ 1 by omega,
      show j ≠ 0 by omega, hj2, hjN]

/-! ## (350) -/

theorem comm350 {N : ℕ} (hN : 4 ≤ N) (ih : IH N) (hsw : E.McSwapAll N) (h333 : H333 N)
    (h334 : H334 N) (h337 : H337 N) (h344 : H344 N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (a c₁ c₂ c₃ : Bool) :
    D.Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N (Kind.sgnZX a) [2] (ctlOr (ctlAt 1 c₂) (ctlOr (ctlAt 0 c₃) (colOn 3 N y)))) := by
  have hc : ∀ i < N, ctlOr (ctlAt 1 c₂) (ctlOr (ctlAt 0 c₃) (colOn 3 N y)) i = none ↔ i = 2 := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i) with h | h | h | h
    · subst h; simp [ctlOr, ctlAt]
    · subst h; simp [ctlOr, ctlAt]
    · subst h; simp [ctlOr, ctlAt, colOn]
    · simp [ctlOr, ctlAt, colOn, show i ≠ 0 by omega, show i ≠ 1 by omega,
        show i ≠ 2 by omega, h, hi]
  have hd := dec_at (by omega) ih hsw h333 h334 a (t := 2) (b := 0) (h := 1) (by omega)
    (by omega) (by omega) (by decide) (by decide) (by decide) _ hc
  refine Comm.congr (Derivable.refl _) hd.symm (comm_dw a ?_ ?_)
  · -- (344)
    have e : mc N .hg [1, 2] (setCtl (ctlOr (ctlAt 1 c₂) (ctlOr (ctlAt 0 c₃) (colOn 3 N y))) 1 none) =
        mc N .hg [1, 2] (ctlOr (ctlAt 0 c₃) (colOn 3 N y)) := Net.mc_congr _ _ _ (fun i hi => by
      by_cases h1 : i = 1
      · subst h1; simp [setCtl, ctlOr, ctlAt, colOn]
      · simp [setCtl, ctlOr, ctlAt, h1])
    rw [e]; exact h344 x y hxy c₁ c₃
  · -- (337)
    obtain ⟨j, hj3, hjN, hxyj⟩ := hxy
    have h := h337 (fun i => if i = 2 then true else y i) (fun i => if i = 2 then c₁ else x i)
      ⟨j, by omega, hjN, by
        intro h; apply hxyj
        simp only [if_neg (show j ≠ 2 by omega)] at h; exact h.symm⟩ c₂
    refine Derivable.symm (Comm.congr (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_)))
      (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_))) h)
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i) with h | h | h | h
      · subst h; simp [setCtl, ctlOr, ctlAt, colOn]
      · subst h; simp [setCtl, ctlOr, ctlAt, colOn]
      · subst h; simp [setCtl, ctlOr, ctlAt, colOn, show 2 < N by omega]
      · simp [setCtl, ctlOr, ctlAt, colOn, show i ≠ 0 by omega, show i ≠ 1 by omega,
          show i ≠ 2 by omega, h, hi, show 2 ≤ i by omega]
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i) with h | h | h | h
      · subst h; simp [ctlOr, ctlAt, colOn]
      · subst h; simp [ctlOr, ctlAt, colOn]
      · subst h; simp [ctlOr, ctlAt, colOn, show 2 < N by omega]
      · simp [ctlOr, ctlAt, colOn, show i ≠ 2 by omega, h, hi, show 2 ≤ i by omega]

/-! ## (351) -/

theorem comm351 {N : ℕ} (hN : 4 ≤ N) (ih : IH N) (hsw : E.McSwapAll N) (h333 : H333 N)
    (h334 : H334 N) (h317 : H317 N) (h335 : H335 N) (h339 : H339 N) (h340 : H340 N)
    (x y : ℕ → Bool) (a b : Bool) :
    D.Comm N (mc N (Kind.sgnZX a) [0] (colOn 1 N x)) (mc N (Kind.sgnZX b) [0] (colOn 1 N y)) := by
  by_cases hxy : DiffOn 1 N x y
  swap
  · -- the same colours: trivial or (317)
    have e : mc N (Kind.sgnZX b) [0] (colOn 1 N y) = mc N (Kind.sgnZX b) [0] (colOn 1 N x) :=
      Net.mc_congr _ _ _ (fun i hi => by
        simp only [colOn]; split_ifs with h
        · rw [show y i = x i from by
            by_contra hne; exact hxy ⟨i, h.1, h.2, Ne.symm hne⟩]
        · rfl)
    rw [e]
    have h := h317 x
    cases a <;> cases b
    · exact Derivable.refl _
    · exact h.1.trans h.2.symm
    · exact h.2.trans h.1.symm
    · exact Derivable.refl _
  obtain ⟨j, hj1, hjN, hxyj⟩ := hxy
  obtain ⟨b₀, h₀, hb1, hb3, hh1, hh3, hbh, hbj, hhj⟩ :
      ∃ b h, 1 ≤ b ∧ b ≤ 3 ∧ 1 ≤ h ∧ h ≤ 3 ∧ b ≠ h ∧ b ≠ j ∧ h ≠ j :=
    ⟨if j = 1 then 2 else 1, if j = 3 then 2 else 3, by split_ifs <;> omega,
      by split_ifs <;> omega, by split_ifs <;> omega, by split_ifs <;> omega,
      by split_ifs <;> omega, by split_ifs <;> omega, by split_ifs <;> omega⟩
  have hc : ∀ z : ℕ → Bool, ∀ i < N, colOn 1 N z i = none ↔ i = 0 := by
    intro z i hi
    rcases (by omega : i = 0 ∨ 1 ≤ i) with h | h
    · subst h; simp [colOn]
    · simp [colOn, show i ≠ 0 by omega, h, hi]
  have dx := dec_at (by omega) ih hsw h333 h334 a (t := 0) (b := b₀) (h := h₀) (by omega)
    (by omega) (by omega) (by omega) (by omega) hbh _ (hc x)
  have dy := dec_at (by omega) ih hsw h333 h334 b (t := 0) (b := b₀) (h := h₀) (by omega)
    (by omega) (by omega) (by omega) (by omega) hbh _ (hc y)
  refine Comm.congr dx.symm dy.symm (comm_dw2 a b ?_ ?_ ?_ ?_)
  · -- (340) on the wires `h₀, 0`
    exact f340 (by omega) ih h340 (p₀ := h₀) (p₁ := 0) (nd2 (by omega))
      (lt2 (by omega) (by omega)) (by simp [setCtl]) (by simp [setCtl, colOn])
      (by full_tac) (by simp [setCtl]) (by simp [setCtl, colOn]) (by full_tac)
  · -- (339) on the wires `b₀, h₀, 0`, the box of `y`
    refine Derivable.symm (f339 (by omega) ih h339 (p₀ := b₀) (p₁ := h₀) (p₂ := 0)
      (nd3 hbh (by omega) (by omega)) (lt3 (by omega) (by omega) (by omega))
      (a₁ := y h₀) (a₂ := true) (h₀ := x b₀) (by simp [setCtl, show b₀ ≠ 0 by omega])
      (by simp [setCtl, colOn, show h₀ ≠ 0 by omega, Ne.symm hbh, hh1, show h₀ < N by omega])
      (by simp [setCtl]) (by full_tac)
      (by simp [setCtl, colOn, hbh, hb1, show b₀ < N by omega]) (by simp [setCtl])
      (by simp [setCtl, colOn]) (by full_tac) (j := j) (u := y j) (v := x j) hjN
      (by simp; omega) ?_ ?_ (Ne.symm hxyj))
    · simp [setCtl, colOn, show j ≠ 0 by omega, show j ≠ b₀ by omega, hj1, hjN]
    · simp [setCtl, colOn, show j ≠ h₀ by omega, hj1, hjN]
  · -- (339) on the wires `b₀, h₀, 0`, the box of `x`
    refine f339 (by omega) ih h339 (p₀ := b₀) (p₁ := h₀) (p₂ := 0)
      (nd3 hbh (by omega) (by omega)) (lt3 (by omega) (by omega) (by omega))
      (a₁ := x h₀) (a₂ := true) (h₀ := y b₀) (by simp [setCtl, show b₀ ≠ 0 by omega])
      (by simp [setCtl, colOn, show h₀ ≠ 0 by omega, Ne.symm hbh, hh1, show h₀ < N by omega])
      (by simp [setCtl]) (by full_tac)
      (by simp [setCtl, colOn, hbh, hb1, show b₀ < N by omega]) (by simp [setCtl])
      (by simp [setCtl, colOn]) (by full_tac) (j := j) (u := x j) (v := y j) hjN
      (by simp; omega) ?_ ?_ hxyj
    · simp [setCtl, colOn, show j ≠ 0 by omega, show j ≠ b₀ by omega, hj1, hjN]
    · simp [setCtl, colOn, show j ≠ h₀ by omega, hj1, hjN]
  · -- (335) on the wire `b₀`
    exact f335 (by omega) ih h335 (p₀ := b₀) (by omega) (by simp [setCtl, show b₀ ≠ 0 by omega])
      (by full_tac) (by simp [setCtl, show b₀ ≠ 0 by omega]) (by full_tac)

/-! ## (352) -/

theorem comm352 {N : ℕ} (hN : 4 ≤ N) (ih : IH N) (hsw : E.McSwapAll N) (h333 : H333 N)
    (h334 : H334 N) (h335 : H335 N) (h339 : H339 N) (h345 : H345 N) (x y : ℕ → Bool)
    (hxy : DiffOn 2 N x y) (a b c₁ c₂ : Bool) :
    D.Comm N (mc N (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
      (mc N (Kind.sgnZX b) [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))) := by
  obtain ⟨j, hj2, hjN, hxyj⟩ := hxy
  obtain ⟨b₀, hb2, hb3, hbj⟩ : ∃ b, 2 ≤ b ∧ b ≤ 3 ∧ b ≠ j :=
    ⟨if j = 2 then 3 else 2, by split_ifs <;> omega, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  have hcA : ∀ i < N, ctlOr (ctlAt 1 c₁) (colOn 2 N x) i = none ↔ i = 0 := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with h | h | h
    · subst h; simp [ctlOr, ctlAt, colOn]
    · subst h; simp [ctlOr, ctlAt]
    · simp [ctlOr, ctlAt, colOn, show i ≠ 0 by omega, show i ≠ 1 by omega, h, hi]
  have hcB : ∀ i < N, ctlOr (ctlAt 0 c₂) (colOn 2 N y) i = none ↔ i = 1 := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with h | h | h
    · subst h; simp [ctlOr, ctlAt]
    · subst h; simp [ctlOr, ctlAt, colOn]
    · simp [ctlOr, ctlAt, colOn, show i ≠ 0 by omega, show i ≠ 1 by omega, h, hi]
  have dA := dec_at (by omega) ih hsw h333 h334 a (t := 0) (b := b₀) (h := 1) (by omega)
    (by omega) (by omega) (by omega) (by decide) (by omega) _ hcA
  have dB := dec_at (by omega) ih hsw h333 h334 b (t := 1) (b := b₀) (h := 0) (by omega)
    (by omega) (by omega) (by omega) (by decide) (by omega) _ hcB
  refine Comm.congr dA.symm dB.symm (comm_dw2 a b ?_ ?_ ?_ ?_)
  · -- (345)
    have e1 : mc N .hg [1, 0] (setCtl (ctlOr (ctlAt 1 c₁) (colOn 2 N x)) 1 none) =
        mc N .hg [1, 0] (colOn 2 N x) := Net.mc_congr _ _ _ (fun i hi => by
      by_cases h1 : i = 1
      · subst h1; simp [setCtl, colOn]
      · simp [setCtl, ctlOr, ctlAt, h1])
    have e2 : mc N .hg [0, 1] (setCtl (ctlOr (ctlAt 0 c₂) (colOn 2 N y)) 0 none) =
        mc N .hg [0, 1] (colOn 2 N y) := Net.mc_congr _ _ _ (fun i hi => by
      by_cases h0 : i = 0
      · subst h0; simp [setCtl, colOn]
      · simp [setCtl, ctlOr, ctlAt, h0])
    rw [e1, e2]; exact h345 x y
  · -- (339) on the wires `b₀, 1, 0`, the box of the second rotation
    refine Derivable.symm (f339 (by omega) ih h339 (p₀ := b₀) (p₁ := 1) (p₂ := 0)
      (nd3 (by omega) (by omega) (by decide)) (lt3 (by omega) (by omega) (by omega))
      (a₁ := true) (a₂ := c₂) (h₀ := x b₀) (by simp [setCtl, show b₀ ≠ 1 by omega])
      (by simp [setCtl]) (by simp [setCtl, ctlOr, ctlAt, show (0 : ℕ) ≠ b₀ by omega])
      (by full_tac) (by simp [setCtl, ctlOr, ctlAt, colOn, show b₀ ≠ 1 by omega, hb2,
        show b₀ < N by omega]) (by simp [setCtl]) (by simp [setCtl, ctlOr, ctlAt, colOn])
      (by full_tac) (j := j) (u := y j) (v := x j) hjN (by simp; omega) ?_ ?_ (Ne.symm hxyj))
    · simp [setCtl, ctlOr, ctlAt, colOn, show j ≠ 1 by omega, show j ≠ b₀ by omega,
        show j ≠ 0 by omega, hj2, hjN]
    · simp [setCtl, ctlOr, ctlAt, colOn, show j ≠ 1 by omega, hj2, hjN]
  · -- (339) on the wires `b₀, 0, 1`, the box of the first rotation
    refine f339 (by omega) ih h339 (p₀ := b₀) (p₁ := 0) (p₂ := 1)
      (nd3 (by omega) (by omega) (by decide)) (lt3 (by omega) (by omega) (by omega))
      (a₁ := true) (a₂ := c₁) (h₀ := y b₀) (by simp [setCtl, show b₀ ≠ 0 by omega])
      (by simp [setCtl]) (by simp [setCtl, ctlOr, ctlAt, show (1 : ℕ) ≠ b₀ by omega])
      (by full_tac) (by simp [setCtl, ctlOr, ctlAt, colOn, show b₀ ≠ 0 by omega, hb2,
        show b₀ < N by omega]) (by simp [setCtl]) (by simp [setCtl, ctlOr, ctlAt, colOn])
      (by full_tac) (j := j) (u := x j) (v := y j) hjN (by simp; omega) ?_ ?_ hxyj
    · simp [setCtl, ctlOr, ctlAt, colOn, show j ≠ 0 by omega, show j ≠ b₀ by omega,
        show j ≠ 1 by omega, hj2, hjN]
    · simp [setCtl, ctlOr, ctlAt, colOn, show j ≠ 0 by omega, hj2, hjN]
  · -- (335) on the wire `b₀`
    exact f335 (by omega) ih h335 (p₀ := b₀) (by omega) (by simp [setCtl, show b₀ ≠ 0 by omega])
      (by full_tac) (by simp [setCtl, show b₀ ≠ 1 by omega]) (by full_tac)

end QCert.RealCliffordCH.Sec8.D.N13.R347

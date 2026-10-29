/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (335)–(345) on any wires

Each canonical commutation of Lemma D.13 between boxes and multi-controlled
`H` gates, moved by the frame of its special wires (`RotDec.comm_frame`):
the gates may sit on any wires `p₀, p₁, …` and carry any colours, given by
their control functions, which must have a control on every other wire.
Only (307) and (313) are used for the frames (`E.mcSwapBH`).  The canonical
equations are hypotheses, in the forms of `N13.lean`.
-/
import QCert.RealCliffordCH.Sec8.D.N13.RotDec

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13.R347

open Circuit Net E Eng

/-! ## The canonical statements -/

abbrev H335 (N : ℕ) : Prop := ∀ x y : ℕ → Bool,
  D.Comm N (mc N .box [0] (colOn 1 N x)) (mc N .box [0] (colOn 1 N y))

abbrev H336 (N : ℕ) : Prop := ∀ (x y : ℕ → Bool) (c₁ c₂ : Bool),
  D.Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
    (mc N .box [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y)))

abbrev H337 (N : ℕ) : Prop := ∀ x y : ℕ → Bool, DiffOn 2 N x y → ∀ c₁ : Bool,
  D.Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x))) (mc N .hg [0, 1] (colOn 2 N y))

abbrev H338 (N : ℕ) : Prop := ∀ (x y : ℕ → Bool) (c₁ : Bool),
  D.Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x))) (mc N .hg [1, 0] (colOn 2 N y))

abbrev H340 (N : ℕ) : Prop := ∀ x y : ℕ → Bool,
  D.Comm N (mc N .hg [0, 1] (colOn 2 N x)) (mc N .hg [0, 1] (colOn 2 N y))

abbrev H344 (N : ℕ) : Prop := ∀ x y : ℕ → Bool, DiffOn 3 N x y → ∀ c₁ c₂ : Bool,
  D.Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
    (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₂) (colOn 3 N y)))

abbrev H345 (N : ℕ) : Prop := ∀ x y : ℕ → Bool,
  D.Comm N (mc N .hg [1, 0] (colOn 2 N x)) (mc N .hg [0, 1] (colOn 2 N y))

/-! ## Moved to any wires -/

section

variable {N : ℕ} (hN : 3 ≤ N) (ih : IH N)
include hN ih

/-- (335): two boxes on the same box wire `p₀`. -/
theorem f335 (h335 : H335 N) {p₀ : ℕ} (hpN : p₀ < N) {dA dB : ℕ → Option Bool}
    (hA0 : dA p₀ = none) (hAf : ∀ i < N, i ∉ [p₀] → dA i ≠ none)
    (hB0 : dB p₀ = none) (hBf : ∀ i < N, i ∉ [p₀] → dB i ≠ none) :
    D.Comm N (mc N .box [p₀] dA) (mc N .box [p₀] dB) := by
  have hp : [p₀].Nodup := by simp
  have hps : ∀ p ∈ [p₀], p < N := by simp [hpN]
  have f0 : frm [p₀] 0 = p₀ := frm_getD hp hps (by simp)
  have hlow : ∀ (d : ℕ → Option Bool), d p₀ = none → ∀ j < [p₀].length,
      colOn 1 N (rd [p₀] d) j = d ([p₀].getD j 0) := by
    intro d hd j hj
    have : j = 0 := by simpa using hj
    subst this; simp [colOn, hd]
  have hhigh : ∀ (d : ℕ → Option Bool), ∀ j, [p₀].length ≤ j → j < N → frm [p₀] j ∉ [p₀] →
      colOn 1 N (rd [p₀] d) j = some (rd [p₀] d j) := by
    intro d j hj hjN _
    have : 1 ≤ j := by simpa using hj
    simp [colOn, this, hjN]
  exact comm_frame (mcSwapBH ih) hp hps (Or.inl rfl) (Or.inl rfl) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0]) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0])
    (frm_ctl hp hps dA _ (hlow dA hA0) (hhigh dA) hAf)
    (frm_ctl hp hps dB _ (hlow dB hB0) (hhigh dB) hBf) (h335 _ _)

/-- (336): two boxes, the box wire of each a control of the other. -/
theorem f336 (h336 : H336 N) {p₀ p₁ : ℕ} (hp : [p₀, p₁].Nodup) (hps : ∀ p ∈ [p₀, p₁], p < N)
    {dA dB : ℕ → Option Bool} {a₁ b₀ : Bool}
    (hA0 : dA p₀ = none) (hA1 : dA p₁ = some a₁) (hAf : ∀ i < N, i ∉ [p₀, p₁] → dA i ≠ none)
    (hB0 : dB p₀ = some b₀) (hB1 : dB p₁ = none) (hBf : ∀ i < N, i ∉ [p₀, p₁] → dB i ≠ none) :
    D.Comm N (mc N .box [p₀] dA) (mc N .box [p₁] dB) := by
  have f0 : frm [p₀, p₁] 0 = p₀ := frm_getD hp hps (by simp)
  have f1 : frm [p₀, p₁] 1 = p₁ := frm_getD hp hps (by simp)
  refine comm_frame (mcSwapBH ih) hp hps (Or.inl rfl) (Or.inl rfl) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0]) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f1])
    (frm_ctl hp hps dA _ ?_ ?_ hAf) (frm_ctl hp hps dB _ ?_ ?_ hBf)
    (h336 (rd [p₀, p₁] dA) (rd [p₀, p₁] dB) a₁ b₀)
  · intro j hj
    rcases (by simp at hj; omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [ctlOr, ctlAt, colOn, hA0, hA1]
  · intro j hj hjN _
    have : 2 ≤ j := by simpa using hj
    simp [ctlOr, ctlAt, colOn, show j ≠ 1 by omega, this, hjN]
  · intro j hj
    rcases (by simp at hj; omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [ctlOr, ctlAt, colOn, hB0, hB1]
  · intro j hj hjN _
    have : 2 ≤ j := by simpa using hj
    simp [ctlOr, ctlAt, colOn, show j ≠ 0 by omega, this, hjN]

/-- (338): a box on `p₀` and a multi-controlled `H` with its box on `p₁`, its
`H` on `p₀`. -/
theorem f338 (h338 : H338 N) {p₀ p₁ : ℕ} (hp : [p₀, p₁].Nodup) (hps : ∀ p ∈ [p₀, p₁], p < N)
    {dA dH : ℕ → Option Bool} {a₁ : Bool}
    (hA0 : dA p₀ = none) (hA1 : dA p₁ = some a₁) (hAf : ∀ i < N, i ∉ [p₀, p₁] → dA i ≠ none)
    (hH0 : dH p₀ = none) (hH1 : dH p₁ = none) (hHf : ∀ i < N, i ∉ [p₀, p₁] → dH i ≠ none) :
    D.Comm N (mc N .box [p₀] dA) (mc N .hg [p₁, p₀] dH) := by
  have f0 : frm [p₀, p₁] 0 = p₀ := frm_getD hp hps (by simp)
  have f1 : frm [p₀, p₁] 1 = p₁ := frm_getD hp hps (by simp)
  refine comm_frame (mcSwapBH ih) hp hps (Or.inl rfl) (Or.inr rfl) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0]) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0, f1])
    (frm_ctl hp hps dA _ ?_ ?_ hAf) (frm_ctl hp hps dH _ ?_ ?_ hHf)
    (h338 (rd [p₀, p₁] dA) (rd [p₀, p₁] dH) a₁)
  · intro j hj
    rcases (by simp at hj; omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [ctlOr, ctlAt, colOn, hA0, hA1]
  · intro j hj hjN _
    have : 2 ≤ j := by simpa using hj
    simp [ctlOr, ctlAt, colOn, show j ≠ 1 by omega, this, hjN]
  · intro j hj
    rcases (by simp at hj; omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [colOn, hH0, hH1]
  · intro j hj hjN _
    have : 2 ≤ j := by simpa using hj
    simp [colOn, this, hjN]

/-- (339): a box on `p₀` and a multi-controlled `H` with its box on `p₁`, its
`H` on `p₂`, separated on a common control. -/
theorem f339 (h339 : R347.H339 N) {p₀ p₁ p₂ : ℕ} (hp : [p₀, p₁, p₂].Nodup)
    (hps : ∀ p ∈ [p₀, p₁, p₂], p < N) {dA dH : ℕ → Option Bool} {a₁ a₂ h₀ : Bool}
    (hA0 : dA p₀ = none) (hA1 : dA p₁ = some a₁) (hA2 : dA p₂ = some a₂)
    (hAf : ∀ i < N, i ∉ [p₀, p₁, p₂] → dA i ≠ none)
    (hH0 : dH p₀ = some h₀) (hH1 : dH p₁ = none) (hH2 : dH p₂ = none)
    (hHf : ∀ i < N, i ∉ [p₀, p₁, p₂] → dH i ≠ none)
    {j : ℕ} {u v : Bool} (hjN : j < N) (hj : j ∉ [p₀, p₁, p₂]) (hAj : dA j = some u)
    (hHj : dH j = some v) (huv : u ≠ v) :
    D.Comm N (mc N .box [p₀] dA) (mc N .hg [p₁, p₂] dH) := by
  have f0 : frm [p₀, p₁, p₂] 0 = p₀ := frm_getD hp hps (by simp)
  have f1 : frm [p₀, p₁, p₂] 1 = p₁ := frm_getD hp hps (by simp)
  have f2 : frm [p₀, p₁, p₂] 2 = p₂ := frm_getD hp hps (by simp)
  refine comm_frame (mcSwapBH ih) hp hps (Or.inl rfl) (Or.inr rfl) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0]) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f1, f2])
    (frm_ctl hp hps dA _ ?_ ?_ hAf) (frm_ctl hp hps dH _ ?_ ?_ hHf)
    (h339 (rd [p₀, p₁, p₂] dA) (rd [p₀, p₁, p₂] dH) (diff_frm hp hps hAj hHj huv hj hjN) a₂ a₁ h₀)
  · intro k hk
    rcases (by simp at hk; omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
      simp [ctlOr, ctlAt, colOn, hA0, hA1, hA2]
  · intro k hk hkN _
    have : 3 ≤ k := by simpa using hk
    simp [ctlOr, ctlAt, colOn, show k ≠ 1 by omega, show k ≠ 2 by omega, this, hkN]
  · intro k hk
    rcases (by simp at hk; omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
      simp [ctlOr, ctlAt, colOn, hH0, hH1, hH2]
  · intro k hk hkN _
    have : 3 ≤ k := by simpa using hk
    simp [ctlOr, ctlAt, colOn, show k ≠ 0 by omega, this, hkN]

/-- (340): two multi-controlled `H` gates on the same wires. -/
theorem f340 (h340 : H340 N) {p₀ p₁ : ℕ} (hp : [p₀, p₁].Nodup) (hps : ∀ p ∈ [p₀, p₁], p < N)
    {dA dB : ℕ → Option Bool}
    (hA0 : dA p₀ = none) (hA1 : dA p₁ = none) (hAf : ∀ i < N, i ∉ [p₀, p₁] → dA i ≠ none)
    (hB0 : dB p₀ = none) (hB1 : dB p₁ = none) (hBf : ∀ i < N, i ∉ [p₀, p₁] → dB i ≠ none) :
    D.Comm N (mc N .hg [p₀, p₁] dA) (mc N .hg [p₀, p₁] dB) := by
  have f0 : frm [p₀, p₁] 0 = p₀ := frm_getD hp hps (by simp)
  have f1 : frm [p₀, p₁] 1 = p₁ := frm_getD hp hps (by simp)
  refine comm_frame (mcSwapBH ih) hp hps (Or.inr rfl) (Or.inr rfl) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0, f1]) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0, f1])
    (frm_ctl hp hps dA _ ?_ ?_ hAf) (frm_ctl hp hps dB _ ?_ ?_ hBf)
    (h340 (rd [p₀, p₁] dA) (rd [p₀, p₁] dB))
  · intro j hj
    rcases (by simp at hj; omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [colOn, hA0, hA1]
  · intro j hj hjN _
    have : 2 ≤ j := by simpa using hj
    simp [colOn, this, hjN]
  · intro j hj
    rcases (by simp at hj; omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [colOn, hB0, hB1]
  · intro j hj hjN _
    have : 2 ≤ j := by simpa using hj
    simp [colOn, this, hjN]

/-- (344): multi-controlled `H` gates on `p₀, p₁` and on `p₁, p₂`, separated
on a common control. -/
theorem f344 (h344 : H344 N) {p₀ p₁ p₂ : ℕ} (hp : [p₀, p₁, p₂].Nodup)
    (hps : ∀ p ∈ [p₀, p₁, p₂], p < N) {dA dB : ℕ → Option Bool} {a₂ b₀ : Bool}
    (hA0 : dA p₀ = none) (hA1 : dA p₁ = none) (hA2 : dA p₂ = some a₂)
    (hAf : ∀ i < N, i ∉ [p₀, p₁, p₂] → dA i ≠ none)
    (hB0 : dB p₀ = some b₀) (hB1 : dB p₁ = none) (hB2 : dB p₂ = none)
    (hBf : ∀ i < N, i ∉ [p₀, p₁, p₂] → dB i ≠ none)
    {j : ℕ} {u v : Bool} (hjN : j < N) (hj : j ∉ [p₀, p₁, p₂]) (hAj : dA j = some u)
    (hBj : dB j = some v) (huv : u ≠ v) :
    D.Comm N (mc N .hg [p₀, p₁] dA) (mc N .hg [p₁, p₂] dB) := by
  have f0 : frm [p₀, p₁, p₂] 0 = p₀ := frm_getD hp hps (by simp)
  have f1 : frm [p₀, p₁, p₂] 1 = p₁ := frm_getD hp hps (by simp)
  have f2 : frm [p₀, p₁, p₂] 2 = p₂ := frm_getD hp hps (by simp)
  refine comm_frame (mcSwapBH ih) hp hps (Or.inr rfl) (Or.inr rfl) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0, f1]) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f1, f2])
    (frm_ctl hp hps dA _ ?_ ?_ hAf) (frm_ctl hp hps dB _ ?_ ?_ hBf)
    (h344 (rd [p₀, p₁, p₂] dA) (rd [p₀, p₁, p₂] dB) (diff_frm hp hps hAj hBj huv hj hjN) a₂ b₀)
  · intro k hk
    rcases (by simp at hk; omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
      simp [ctlOr, ctlAt, colOn, hA0, hA1, hA2]
  · intro k hk hkN _
    have : 3 ≤ k := by simpa using hk
    simp [ctlOr, ctlAt, colOn, show k ≠ 2 by omega, this, hkN]
  · intro k hk
    rcases (by simp at hk; omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
      simp [ctlOr, ctlAt, colOn, hB0, hB1, hB2]
  · intro k hk hkN _
    have : 3 ≤ k := by simpa using hk
    simp [ctlOr, ctlAt, colOn, show k ≠ 0 by omega, this, hkN]

/-- (345): multi-controlled `H` gates on `p₁, p₀` and on `p₀, p₁`. -/
theorem f345 (h345 : H345 N) {p₀ p₁ : ℕ} (hp : [p₀, p₁].Nodup) (hps : ∀ p ∈ [p₀, p₁], p < N)
    {dA dB : ℕ → Option Bool}
    (hA0 : dA p₀ = none) (hA1 : dA p₁ = none) (hAf : ∀ i < N, i ∉ [p₀, p₁] → dA i ≠ none)
    (hB0 : dB p₀ = none) (hB1 : dB p₁ = none) (hBf : ∀ i < N, i ∉ [p₀, p₁] → dB i ≠ none) :
    D.Comm N (mc N .hg [p₁, p₀] dA) (mc N .hg [p₀, p₁] dB) := by
  have f0 : frm [p₀, p₁] 0 = p₀ := frm_getD hp hps (by simp)
  have f1 : frm [p₀, p₁] 1 = p₁ := frm_getD hp hps (by simp)
  refine comm_frame (mcSwapBH ih) hp hps (Or.inr rfl) (Or.inr rfl) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0, f1]) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0, f1])
    (frm_ctl hp hps dA _ ?_ ?_ hAf) (frm_ctl hp hps dB _ ?_ ?_ hBf)
    (h345 (rd [p₀, p₁] dA) (rd [p₀, p₁] dB))
  · intro j hj
    rcases (by simp at hj; omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [colOn, hA0, hA1]
  · intro j hj hjN _
    have : 2 ≤ j := by simpa using hj
    simp [colOn, this, hjN]
  · intro j hj
    rcases (by simp at hj; omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [colOn, hB0, hB1]
  · intro j hj hjN _
    have : 2 ≤ j := by simpa using hj
    simp [colOn, this, hjN]

end

end QCert.RealCliffordCH.Sec8.D.N13.R347

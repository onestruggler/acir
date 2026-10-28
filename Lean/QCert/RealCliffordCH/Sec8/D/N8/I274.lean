/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (274) in the conventions of the interface

`S274.s274` on five local wires gives (274) from five wires on.  On three
and four wires the box without its idle wire is `Z` on wire `2`, resp. `CZ`
of the wires `2, 3`, a circuit idle on both wires `0` and `1`, so two
semantic steps (Lemma 5.1, with wire `0` and with wire `1` removed) suffice.
-/
import QCert.RealCliffordCH.Sec8.D.N8.S274

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

theorem wc_one (K N : ℕ) (x : Lt) : wc K N [x] = x.circ K N := by
  simp [wc, drawn]

/-- Black controls on the local wires `lo, …, K - 1` and the bulk, read as
`blackOn lo N`. -/
theorem ctl_black {K N lo : ℕ} (cs : List (ℕ × Bool))
    (hcs : ∀ i < K, cs.lookup i = if lo ≤ i then some true else none) (hlo : lo ≤ K) :
    ∀ i < N, ctl K cs true i = blackOn lo N i := by
  intro i hi
  simp only [ctl, blackOn]
  by_cases hik : i < K
  · rw [if_pos hik, hcs i hik]
    by_cases h : lo ≤ i
    · rw [if_pos h, if_pos ⟨h, hi⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.1)]
  · simp [if_neg hik, show lo ≤ i ∧ i < N from ⟨by omega, hi⟩]

theorem B1_mc (N : ℕ) : wc 5 N [B1] = mc N .box [1] (blackOn 2 N) := by
  rw [wc_one, B1_eq]
  exact mc_congr N .box [1] (ctl_black _ (fun i hi => by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      rfl) (by omega))

theorem B0_mc (N : ℕ) : wc 5 N [B0] = mc N .box [0] (blackOn 2 N) := by
  rw [wc_one, B0_eq]
  exact mc_congr N .box [0] (ctl_black _ (fun i hi => by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      rfl) (by omega))

/-! ## Three and four wires -/

def b1_3 : Lt := .g .box [1] [(2, true)] false
def b0_3 : Lt := .g .box [0] [(2, true)] false

theorem run274_3 : check 2 [] [b1_3] [b0_3] [.sem 0 1 [.s (.Z 2)] 0, .sem 0 1 [b0_3] 1] = true := by
  decide +kernel

def b1_4 : Lt := .g .box [1] [(2, true), (3, true)] false
def b0_4 : Lt := .g .box [0] [(2, true), (3, true)] false

theorem run274_4 : check 3 [] [b1_4] [b0_4] [.sem 0 1 [.s (.C 2)] 0, .sem 0 1 [b0_4] 1] = true := by
  decide +kernel

/-- (274) in the conventions of `MC`, at every width from three on. -/
theorem eq274' (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (mc N .box [1] (blackOn 2 N)) (mc N .box [0] (blackOn 2 N)) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · have h := check_sound (frame 2) (m := 0) ih (T := []) (fun _ h => by simp at h) run274_3
    rw [wc_one, wc_one] at h
    rw [mc_congr 3 .box [1] (c' := ctl 3 [(2, true)] false) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl),
        mc_congr 3 .box [0] (c' := ctl 3 [(2, true)] false) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl)]
    exact h
  · have h := check_sound (frame 3) (m := 0) ih (T := []) (fun _ h => by simp at h) run274_4
    rw [wc_one, wc_one] at h
    rw [mc_congr 4 .box [1] (c' := ctl 4 [(2, true), (3, true)] false) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl),
        mc_congr 4 .box [0] (c' := ctl 4 [(2, true), (3, true)] false) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl)]
    exact h
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    have h := s274 m ih
    rw [B1_mc, B0_mc] at h
    exact h

end QCert.RealCliffordCH.Sec8.D.N8

/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (277) in the conventions of the interface

`S277.s277` gives (277) from five wires on.  On three and four wires the
multi-controlled `H` without its idle wire is `H` on wire `2`, resp. `CH` from
wire `3` onto wire `2`, idle on both wires `0` and `1`: two semantic steps.
-/
import QCert.RealCliffordCH.Sec8.D.N8.S277
import QCert.RealCliffordCH.Sec8.D.N8.I274

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

theorem hg12_mc (N : ℕ) : wc 5 N [hg12] = mc N .hg [1, 2] (blackOn 3 N) := by
  rw [wc_one]
  exact mc_congr N .hg [1, 2] (ctl_black _ (fun i hi => by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      rfl) (by omega))

theorem hg02_mc (N : ℕ) : wc 5 N [hg02] = mc N .hg [0, 2] (blackOn 3 N) := by
  rw [wc_one, hg02_eq]
  exact mc_congr N .hg [0, 2] (ctl_black _ (fun i hi => by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      rfl) (by omega))

def h12_3 : Lt := .g .hg [1, 2] [] false
def h02_3 : Lt := .g .hg [0, 2] [] false

theorem run277_3 : check 2 [] [h12_3] [h02_3] [.sem 0 1 [.s (.H 2)] 0, .sem 0 1 [h02_3] 1] = true := by
  decide +kernel

def h12_4 : Lt := .g .hg [1, 2] [(3, true)] false
def h02_4 : Lt := .g .hg [0, 2] [(3, true)] false

theorem run277_4 : check 3 [] [h12_4] [h02_4] [.sem 0 1 [.s (.K 2)] 0, .sem 0 1 [h02_4] 1] = true := by
  decide +kernel

/-- (277) in the conventions of `MC`, at every width from three on. -/
theorem eq277' (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (mc N .hg [1, 2] (blackOn 3 N)) (mc N .hg [0, 2] (blackOn 3 N)) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · have h := check_sound (frame 2) (m := 0) ih (T := []) (fun _ h => by simp at h) run277_3
    rw [wc_one, wc_one] at h
    rw [mc_congr 3 .hg [1, 2] (c' := ctl 3 [] false) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl),
        mc_congr 3 .hg [0, 2] (c' := ctl 3 [] false) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl)]
    exact h
  · have h := check_sound (frame 3) (m := 0) ih (T := []) (fun _ h => by simp at h) run277_4
    rw [wc_one, wc_one] at h
    rw [mc_congr 4 .hg [1, 2] (c' := ctl 4 [(3, true)] false) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl),
        mc_congr 4 .hg [0, 2] (c' := ctl 4 [(3, true)] false) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl)]
    exact h
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    have h := s277 m ih
    rw [hg12_mc, hg02_mc] at h
    exact h

end QCert.RealCliffordCH.Sec8.D.N8

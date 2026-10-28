/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Symmetries of the canonical gates on four wires

`CanonSym K k` for the canonical gates that fit on four wires: below the
full width from completeness (`WS.canonSym_small`), the box with three
controls from (157) and (161), the multi-controlled `H` with two controls
from (162).  `avail4a` lists them, for `WS.rel_entry`.
-/
import QCert.RealCliffordCH.Sec8.D.W3.Sym
import QCert.RealCliffordCH.Sec8.D.W4.A

namespace QCert.RealCliffordCH.Sec8.D.W4

open Circuit WE WS Net
open Eng (L)

/-- The canonical gates on at most three wires, the box with three controls and
the multi-controlled `H` with two. -/
def avail4a (K : Kind) (k : ℕ) : Bool :=
  decide (k + kindSp K ≤ 3) || (K == .box && k == 3) || (K == .hg && k == 2)

theorem canon_box3 : canonC .box 3 = mc 4 .box [0] (SE.ctl 4 [(3, true), (2, true), (1, true)] false) := by
  rw [← mc_canon]
  exact mc_congr 4 .box [0] (fun i hi => by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl)

theorem canon_hg2 : canonC .hg 2 = mc 4 .hg [0, 1] (SE.ctl 4 [(3, true), (2, true)] false) := by
  rw [← mc_canon]
  exact mc_congr 4 .hg [0, 1] (fun i hi => by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl)

set_option maxRecDepth 100000 in
theorem canonSym_box3 (ih : IH 4) : CanonSym .box 3 := by
  intro u hu hu2
  have hu' : u = 1 ∨ u = 2 := by simp only [kindSp] at hu hu2; omega
  show Derivable (theory 4) (drawn [swAt 4 u, canonC .box 3, swAt 4 u]) (canonC .box 3)
  rw [canon_box3]
  rcases hu' with rfl | rfl
  · exact t157 ih
  · exact t161 ih

set_option maxRecDepth 100000 in
theorem canonSym_hg2 (ih : IH 4) : CanonSym .hg 2 := by
  intro u hu hu2
  have hu' : u = 2 := by simp only [kindSp] at hu hu2; omega
  subst hu'
  show Derivable (theory 4) (drawn [swAt 4 2, canonC .hg 2, swAt 4 2]) (canonC .hg 2)
  rw [canon_hg2]
  exact t162 ih

theorem havail4a (ih : IH 4) : ∀ K k, avail4a K k = true → CanonSym K k := by
  intro K k h
  simp only [avail4a, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with (h | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
  · cases K <;> simp only [kindSp] at h
    · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
        exact canonSym_small ih _ _ (by simp [kindSp]) (by decide +kernel)
    · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
        exact canonSym_small ih _ _ (by simp [kindSp]) (by decide +kernel)
    · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
        exact canonSym_small ih _ _ (by simp [kindSp]) (by decide +kernel)
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;>
        exact canonSym_small ih _ _ (by simp [kindSp]) (by decide +kernel)
  · exact canonSym_box3 ih
  · exact canonSym_hg2 ih

/-! ## A test: (168) relabelled -/

example (ih : IH 4) : Derivable (theory 4)
    (wcT 4 [rlS [2, 1] (tp 2 [L.C 0] [0, 2]), rlS [2, 1] (tg .zx [1] [(3, true), (2, true)])])
    (wcT 4 [rlS [2, 1] (tg .zx [1] [(3, true), (2, true)]), rlS [2, 1] (tp 2 [L.C 0] [0, 2])]) :=
  rel_entry (havail4a ih) [2, 1] (by decide +kernel) (t168 ih)

end QCert.RealCliffordCH.Sec8.D.W4

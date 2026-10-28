/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Control symmetries of all canonical gates on four wires

Equations (214) and (215) give the two adjacent control transpositions
for ZX and XZ. The other full-width gates are covered by `avail4a`.
-/
import QCert.RealCliffordCH.Sec8.D.W4.Expansion

namespace QCert.RealCliffordCH.Sec8.D.W4

open Circuit WE WS Net
open Eng (L)

set_option maxRecDepth 100000

def avail4b (K : Kind) (k : Nat) : Bool :=
  avail4a K k || ((K == .zx || K == .xz) && k == 3)

theorem canon_zx3 :
    canonC .zx 3 = mc 4 .zx [0] (SE.ctl 4 [(3, true), (2, true), (1, true)] false) := by
  rw [← mc_canon]
  apply mc_congr _ _ _
  intro i hi
  simp only [kindSp] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem canon_xz3 :
    canonC .xz 3 = mc 4 .xz [0] (SE.ctl 4 [(3, true), (2, true), (1, true)] false) := by
  rw [← mc_canon]
  apply mc_congr _ _ _
  intro i hi
  simp only [kindSp] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem canonSym_zx3 (ih : IH 4) : CanonSym .zx 3 := by
  intro u hu hu2
  have hu' : u = 1 ∨ u = 2 := by simp only [kindSp] at hu hu2; omega
  show Derivable (theory 4) (drawn [swAt 4 u, canonC .zx 3, swAt 4 u]) (canonC .zx 3)
  rw [canon_zx3]
  rcases hu' with rfl | rfl
  · exact check_sound ih (AllD.cons (t215F ih) (AllD.nil 4))
      (w := [tS 1, tg .zx [0] [(3, true), (2, true), (1, true)], tS 1])
      (v := [tg .zx [0] [(3, true), (2, true), (1, true)]])
      (ss := [.rw 1 0 false, .sem 0 2 [] 0]) (by decide +kernel)
  · exact check_sound ih (AllD.cons (t214F ih) (AllD.nil 4))
      (w := [tS 2, tg .zx [0] [(3, true), (2, true), (1, true)], tS 2])
      (v := [tg .zx [0] [(3, true), (2, true), (1, true)]])
      (ss := [.rw 1 0 false, .sem 0 2 [] 0]) (by decide +kernel)

theorem canonSym_xz3 (ih : IH 4) : CanonSym .xz 3 := by
  intro u hu hu2
  have hu' : u = 1 ∨ u = 2 := by simp only [kindSp] at hu hu2; omega
  show Derivable (theory 4) (drawn [swAt 4 u, canonC .xz 3, swAt 4 u]) (canonC .xz 3)
  rw [canon_xz3]
  rcases hu' with rfl | rfl
  · exact check_sound ih (AllD.cons (t215T ih) (AllD.nil 4))
      (w := [tS 1, tg .xz [0] [(3, true), (2, true), (1, true)], tS 1])
      (v := [tg .xz [0] [(3, true), (2, true), (1, true)]])
      (ss := [.rw 1 0 false, .sem 0 2 [] 0]) (by decide +kernel)
  · exact check_sound ih (AllD.cons (t214T ih) (AllD.nil 4))
      (w := [tS 2, tg .xz [0] [(3, true), (2, true), (1, true)], tS 2])
      (v := [tg .xz [0] [(3, true), (2, true), (1, true)]])
      (ss := [.rw 1 0 false, .sem 0 2 [] 0]) (by decide +kernel)

theorem havail4b (ih : IH 4) : ∀ K k, avail4b K k = true → CanonSym K k := by
  intro K k h
  simp only [avail4b, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h | ⟨hK, rfl⟩
  · exact havail4a ih K k h
  · rcases hK with rfl | rfl
    · exact canonSym_zx3 ih
    · exact canonSym_xz3 ih

end QCert.RealCliffordCH.Sec8.D.W4

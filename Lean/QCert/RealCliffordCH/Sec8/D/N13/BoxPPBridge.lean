/-
Copyright (c) 2026 QCert contributors. All rights reserved.

The three-local-wire semantic commutation lifted across an idle wire.
-/
import QCert.RealCliffordCH.Sec8.D.N13.BoxPPIdle

namespace QCert.RealCliffordCH.Sec8.D.N13
open Circuit Eng SE Net N8 Sim

theorem toTop_pp (m : ℕ) :
    ToTop (m + 4) 3 (pp : Circ (m + 5)) (pp : Circ (m + 4)) := by
  have hK := ToTop.letter (M := m + 4) (q := 3) (by omega) (.K 0) (by simp [L.lo, L.wd])
    (Or.inr (by decide))
  have hH := ToTop.letter (M := m + 4) (q := 3) (by omega) (.H 1) (by simp [L.lo, L.wd])
    (Or.inr (by decide))
  have hZ := ToTop.letter (M := m + 4) (q := 3) (by omega) (.Z 0) (by simp [L.lo, L.wd])
    (Or.inr (by decide))
  have hS := ToTop.letter (M := m + 4) (q := 3) (by omega) (.S 0) (by simp [L.lo, L.wd])
    (Or.inr (by decide))
  exact ToTop.ofList (.cons hK (.cons hH (.cons hZ (.cons hK (.cons hH
    (.cons hZ (.cons hK (.cons hH (.cons hZ (.cons hS .nil))))))))))

def boxCtl4 (N : ℕ) (one b d : Bool) (x : ℕ → Bool) : ℕ → Option Bool :=
  ctlOr (boxCtl one b d) (colOn 4 N x)

theorem commBBpp (m : ℕ) (ih : IH (m + 5)) (u v b c : Bool) (x y : ℕ → Bool) :
    Comm (m + 5) (mc (m + 5) .box [boxTarget u] (boxCtl4 (m + 5) u b true x))
      ((pp : Circ (m + 5)) * mc (m + 5) .box [boxTarget v] (boxCtl4 (m + 5) v c false y) * pp) := by
  have drop : ∀ z : Bool, Net.dropW 3 (boxTarget z) = boxTarget z := by decide
  have lt : ∀ z : Bool, boxTarget z < 2 := by decide
  have mk : ∀ (z e d : Bool) (w : ℕ → Bool),
      ToTop (m + 4) 3 (mc (m + 5) .box [boxTarget z] (boxCtl4 (m + 5) z e d w))
        (mc (m + 4) .box [boxTarget z] (boxCtl4 (m + 5) z e d w ∘ liftW 3)) := by
    intro z e d w
    have h := ToTop.mc (M := m + 4) (q := 3) (by omega) .box [boxTarget z]
      (boxCtl4 (m + 5) z e d w) rfl (by simp)
      (by intro t ht; obtain rfl := List.mem_singleton.1 ht; have := lt z; omega)
      (by simp; have := lt z; omega)
      (by cases z <;> simp [boxCtl4, boxCtl, ctlOr, ctlAt, colOn])
    simpa only [List.map_singleton, drop] using h
  have hA := mk u b true x
  have hB := ((toTop_pp m).mul (mk v c false y)).mul (toTop_pp m)
  refine semIdle ih (ToTop.ofList (.cons hA (.cons hB .nil)))
    (ToTop.ofList (.cons hB (.cons hA .nil))) ?_
  apply box_pp_sem (m + 1) u v b c
  all_goals
    intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl | rfl <;>
      simp [Function.comp, boxCtl4, boxCtl, liftW, ctlOr, ctlAt, colOn]

end QCert.RealCliffordCH.Sec8.D.N13

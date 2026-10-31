/- Copyright (c) 2026 QCert contributors. All rights reserved. -/
import QCert.CliffordCS3.Two.FastCheck
import QCert.CliffordCS3.Replay

namespace QCert.CliffordCS3

/-- Digits used by the kernel-checked rewrite certificates. -/
def gcode3 : Gen → ℕ
  | .i => 1 | .K₀ => 2 | .K₁ => 3 | .K₂ => 4
  | .S₀ => 5 | .S₁ => 6 | .S₂ => 7 | .CS₀₁ => 8 | .CS₁₂ => 9

theorem gcode3_bounds : ∀ a, 0 < gcode3 a ∧ gcode3 a < 16 := by decide

theorem gcode3_inj : Function.Injective gcode3 := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

end QCert.CliffordCS3

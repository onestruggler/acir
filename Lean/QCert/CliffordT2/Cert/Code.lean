/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Coding the letters of two-qubit Clifford+T words

The letters `ω, H₀, H₁, S₀, S₁, T₀, T₁, CZ` as the digits `1 … 8`, for the
replay of certificates on coded words (`QCert.FastRewrite`).
-/
import QCert.CliffordT2.Syntax
import QCert.CliffordT2.FastRewrite

namespace QCert.CliffordT2

/-- The digit of a letter. -/
def gcode : Gen → ℕ
  | .ω => 1 | .H₀ => 2 | .H₁ => 3 | .S₀ => 4 | .S₁ => 5 | .T₀ => 6 | .T₁ => 7 | .CZ => 8

theorem gcode_bounds : ∀ a, 0 < gcode a ∧ gcode a < 16 := by decide

theorem gcode_inj : Function.Injective gcode := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

end QCert.CliffordT2

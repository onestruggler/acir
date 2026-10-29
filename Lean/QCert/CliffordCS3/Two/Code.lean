/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two qubits: coding the letters

The letters `i, K_u, K_l, S_u, S_l, CS` as the digits `1 … 6`, for the
replay of certificates on coded words (`QCert.FastRewrite`), and the
decoding of the macro letters of `U₄(ℤ[1/2, i])` as words on a pair.
-/
import QCert.CliffordCS3.Two.Syntax
import QCert.CliffordCS3.Macro.Basic

namespace QCert.CliffordCS3.Two

/-- The digit of a letter. -/
def gcode2 : Gen2 → ℕ
  | .i => 1 | .Ku => 2 | .Kl => 3 | .Su => 4 | .Sl => 5 | .CS => 6

theorem gcode2_bounds : ∀ a, 0 < gcode2 a ∧ gcode2 a < 16 := by decide

theorem gcode2_inj : Function.Injective gcode2 := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

end QCert.CliffordCS3.Two

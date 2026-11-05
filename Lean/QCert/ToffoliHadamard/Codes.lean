/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): the letters of `Σ₁` as codes

The tables of `Engine.lean` are replayed on words coded as numbers; `κ1`
codes the 25 letters of `Σ₁` by `1 … 25`, so that every letter is good and
`κ1` is injective (`κ1_inj`, decided).
-/
import QCert.ToffoliHadamard.Engine
import QCert.ToffoliHadamard.Syntax
import Mathlib.Tactic.DeriveFintype

namespace QCert.ToffoliHadamard

deriving instance Fintype for Sym1

/-- The code of a letter of `Σ₁`, in `1 … 25`. -/
def κ1 : Sym1 → ℕ
  | .X0 => 1 | .X1 => 2 | .X2 => 3
  | .CX01 => 4 | .CX02 => 5 | .CX10 => 6 | .CX12 => 7 | .CX20 => 8 | .CX21 => 9
  | .CCX01 => 10 | .CCX02 => 11 | .CCX12 => 12
  | .Z0 => 13 | .Z1 => 14 | .Z2 => 15
  | .CZ01 => 16 | .CZ02 => 17 | .CZ12 => 18
  | .K01 => 19 | .K12 => 20
  | .S01 => 21 | .S02 => 22 | .S12 => 23
  | .Kc => 24 | .CCZ => 25

theorem κ1_injective : ∀ a b : Sym1, κ1 a = κ1 b → a = b := by decide +kernel

theorem κ1_inj : ∀ a b : Sym1, Engine.Good κ1 a → κ1 a = κ1 b → a = b :=
  fun a b _ h => κ1_injective a b h

end QCert.ToffoliHadamard

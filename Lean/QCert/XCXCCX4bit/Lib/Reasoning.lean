/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equational reasoning in a fragment's theory

Translation of the part of `Examples/Independence/Reasoning.agda` that the
four-bit development uses (its module `Theory`): an axiom on the bottom
wires of a circuit of any width (`ax_at`, by `CircuitProp.pad`, for the
arities up to four that the fragments have) and lifting a derivation one
wire up (`lift`).  The Agda's `ax-at a k : (n + k) ⊢ w ↓ᵏ k ≈ v ↓ᵏ k` is
`ax_at a k : Der SRel (k + n) (pad k w) (pad k v)` here, the framework's
padding putting the idle wires first in the width; its hidden argument
`T (n ≤ᵇ 4)` is the auto-parameter `hk`.  The module `Width` (setoid
reasoning at a fixed width) is not used by the four-bit development and is
not translated.
-/
import QCert.XCXCCX4bit.Lib.CircuitProp

namespace QCert.XCXCCX4bit.Reasoning

open QCert QCert.Circuit CircuitProp

variable {Gate : ℕ → Type} [HasSwap Gate] {SRel : CRel Gate}

/-- The axiom `a`, of arity `k ≤ 4`, on the bottom wires of a circuit of
`n + k` wires. -/
theorem ax_at {k : ℕ} {w v : Circuit Gate k} (a : SRel k w v) (n : ℕ)
    (hk : k ≤ 4 := by decide) : Der SRel (n + k) (Circuit.pad n w) (Circuit.pad n v) :=
  pad hk (srel_rule a) n

/-- A derivation, one wire up. -/
theorem lift {n : ℕ} {w v : Circuit Gate n} (d : Der SRel n w v) :
    Der SRel (n + 1) (shift w) (shift v) :=
  lemma_cong_up d

end QCert.XCXCCX4bit.Reasoning

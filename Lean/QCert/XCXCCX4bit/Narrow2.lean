/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two-wire steps in derivations on more wires

Translation of `Narrow2.agda`.  `by2 l r h` turns two letter lists on two
wires with the same function (decided: `h : same 2 ⟪l⟫ ⟪r⟫ = true`, by
`decide +kernel`, where the Agda's is `refl`) into an equation of the proof
engine on the bottom two wires of a circuit of any width: completeness on
two wires (`Width2.complete₂`), padded (`CircuitProp.pad₂`).  `liftE`
moves it up, so any two-wire step on adjacent wires is one rewrite.

The Agda's `⟪map⟫` (a letter list mapped is the word mapped) is
`ofList_map`, which holds by `rfl`, words being lists.
-/
import QCert.XCXCCX4bit.Width2

namespace QCert.XCXCCX4bit

open QCert QCert.Circuit CircuitProp IndepProp Engine

variable {k m n : ℕ}

/-- A letter list mapped is the word mapped. -/
theorem ofList_map (f : Gn m → Gn k) (xs : List (Gn m)) :
    FreeMonoid.ofList (xs.map f) = FreeMonoid.map f (FreeMonoid.ofList xs) := rfl

/-- Two two-wire letter lists with the same function, on the bottom two
wires of any circuit. -/
def by2 (l r : List (Gn 2)) (h : same 2 (FreeMonoid.ofList l) (FreeMonoid.ofList r) = true) :
    Eqn (n + 2) :=
  ⟨l.map (Gen.pad n), r.map (Gen.pad n), pad₂ (Width2.complete₂ (same_sound _ _ h)) n⟩

end QCert.XCXCCX4bit

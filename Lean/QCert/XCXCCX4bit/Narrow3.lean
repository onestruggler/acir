/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Three-wire steps in derivations on more wires

Translation of `Narrow3.agda`.  Completeness on three wires
(`Width3.complete₃`), used in two ways.  `by3 l r h` is `Narrow2.by2` one
wire wider: two letter lists on three wires with the same function
(decided, `h : same 3 ⟪l⟫ ⟪r⟫ = true` by `decide +kernel`, where the Agda's
is `refl`) give an equation of the proof engine on the bottom three wires of
a circuit of any width (`CircuitProp.pad₃`), which `liftE` moves up.  And
`Placed`'s section `Narrow` at it: two words of placed letters on any three
of the four wires with the same function are equal (`Narrow3.narrow`,
`Narrow3.narrowP`, `Narrow3.narrow_low`), which `PlacedEngine`'s narrow
steps use.

**Deviation from the Agda.**  The Agda opens `Placed.Narrow complete₃`
publicly, so its `narrow`, `narrowᵖ`, `narrow-low` are the module's own
names.  Here they are definitions in the namespace `Narrow3` that apply
`Placed.narrow …` to `Width3.complete₃` (`Placed`'s own take `complete₃` as
their first argument, so with `Placed` open write `Narrow3.narrowP`).
`by3` is in the flat namespace `QCert.XCXCCX4bit`, as `Narrow2`'s `by2`.
-/
import QCert.XCXCCX4bit.Narrow2
import QCert.XCXCCX4bit.Width3
import QCert.XCXCCX4bit.Placed

namespace QCert.XCXCCX4bit

open QCert QCert.Circuit CircuitProp IndepProp Engine

variable {n : ℕ}

/-- Two three-wire letter lists with the same function, on the bottom three
wires of any circuit. -/
def by3 (l r : List (Gn 3)) (h : same 3 (FreeMonoid.ofList l) (FreeMonoid.ofList r) = true) :
    Eqn (n + 3) :=
  ⟨l.map (Gen.pad n), r.map (Gen.pad n), pad₃ (Width3.complete₃ (same_sound _ _ h)) n⟩

/-- The Toffoli is an involution, on the bottom wires of four. -/
private def by3_test : Eqn 4 := by3 (n := 1) [CCXₗ, CCXₗ] [] (by decide +kernel)

namespace Narrow3

open Placed

/-- Placed letters on the three wires other than `m`, completeness on three
wires (`Placed.narrow` at `Width3.complete₃`). -/
theorem narrow (m : Wire) (u v : List PG) (hu : every (avoids m) u = true)
    (hv : every (avoids m) v = true) (e : sem (ιs u) ≐ sem (ιs v)) : 4 ⊢ ιs u ≈ ιs v :=
  Placed.narrow @Width3.complete₃ m u v hu hv e

/-- The same, from the functions of the letters (the Agda's `narrowᵖ`). -/
theorem narrowP (m : Wire) (u v : List PG) (hu : every (avoids m) u = true)
    (hv : every (avoids m) v = true) (e : semPs u ≐ semPs v) : 4 ⊢ ιs u ≈ ιs v :=
  Placed.narrowP @Width3.complete₃ m u v hu hv e

/-- On the bottom three wires (the Agda's `narrow-low`). -/
theorem narrow_low (u v : List PG) (hu : every (avoids 3) u = true)
    (hv : every (avoids 3) v = true) (e : sem (ιs u) ≐ sem (ιs v)) : 4 ⊢ ιs u ≈ ιs v :=
  Placed.narrow_low @Width3.complete₃ u v hu hv e

end Narrow3

end QCert.XCXCCX4bit

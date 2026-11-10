/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The numbering of the sixteen states of four wires along the reflected Gray code

Translation of `Numbering.agda`.  Position `i` is the state `i xor (i >> 1)`,
bit `k` of it on wire `k`, so that wire 0 changes most often and two
consecutive states differ on one wire.  Vectors list wire 0 first: position
1 is `1000` below, the state with wire 0 set.  `enc` and `dec` are the
numbering and its inverse.

**Deviation from the Agda.**  The Agda's `fin16`, which takes a statement
about the sixteen positions apart into its sixteen cases for proofs by
evaluation at each, is not needed: such statements are decided (`decide`).
-/
import QCert.Alt16RevCir.Semantics

namespace QCert.Alt16RevCir

/-! ## The numbering -/

/-- The state at a position, the bit of wire 0 first. -/
def enc : Fin 16 → Bits 4
  | 0 => false ∷ false ∷ false ∷ false ∷ .nil
  | 1 => true ∷ false ∷ false ∷ false ∷ .nil
  | 2 => true ∷ true ∷ false ∷ false ∷ .nil
  | 3 => false ∷ true ∷ false ∷ false ∷ .nil
  | 4 => false ∷ true ∷ true ∷ false ∷ .nil
  | 5 => true ∷ true ∷ true ∷ false ∷ .nil
  | 6 => true ∷ false ∷ true ∷ false ∷ .nil
  | 7 => false ∷ false ∷ true ∷ false ∷ .nil
  | 8 => false ∷ false ∷ true ∷ true ∷ .nil
  | 9 => true ∷ false ∷ true ∷ true ∷ .nil
  | 10 => true ∷ true ∷ true ∷ true ∷ .nil
  | 11 => false ∷ true ∷ true ∷ true ∷ .nil
  | 12 => false ∷ true ∷ false ∷ true ∷ .nil
  | 13 => true ∷ true ∷ false ∷ true ∷ .nil
  | 14 => true ∷ false ∷ false ∷ true ∷ .nil
  | 15 => false ∷ false ∷ false ∷ true ∷ .nil
  | ⟨k + 16, h⟩ => absurd h (by omega)

/-- The position of a state. -/
def dec : Bits 4 → Fin 16
  | false ∷ false ∷ false ∷ false ∷ .nil => 0
  | true ∷ false ∷ false ∷ false ∷ .nil => 1
  | true ∷ true ∷ false ∷ false ∷ .nil => 2
  | false ∷ true ∷ false ∷ false ∷ .nil => 3
  | false ∷ true ∷ true ∷ false ∷ .nil => 4
  | true ∷ true ∷ true ∷ false ∷ .nil => 5
  | true ∷ false ∷ true ∷ false ∷ .nil => 6
  | false ∷ false ∷ true ∷ false ∷ .nil => 7
  | false ∷ false ∷ true ∷ true ∷ .nil => 8
  | true ∷ false ∷ true ∷ true ∷ .nil => 9
  | true ∷ true ∷ true ∷ true ∷ .nil => 10
  | false ∷ true ∷ true ∷ true ∷ .nil => 11
  | false ∷ true ∷ false ∷ true ∷ .nil => 12
  | true ∷ true ∷ false ∷ true ∷ .nil => 13
  | true ∷ false ∷ false ∷ true ∷ .nil => 14
  | false ∷ false ∷ false ∷ true ∷ .nil => 15

theorem dec_enc : ∀ i, dec (enc i) = i := by decide

theorem enc_dec : ∀ x, enc (dec x) = x
  | false ∷ false ∷ false ∷ false ∷ .nil => rfl
  | true ∷ false ∷ false ∷ false ∷ .nil => rfl
  | true ∷ true ∷ false ∷ false ∷ .nil => rfl
  | false ∷ true ∷ false ∷ false ∷ .nil => rfl
  | false ∷ true ∷ true ∷ false ∷ .nil => rfl
  | true ∷ true ∷ true ∷ false ∷ .nil => rfl
  | true ∷ false ∷ true ∷ false ∷ .nil => rfl
  | false ∷ false ∷ true ∷ false ∷ .nil => rfl
  | false ∷ false ∷ true ∷ true ∷ .nil => rfl
  | true ∷ false ∷ true ∷ true ∷ .nil => rfl
  | true ∷ true ∷ true ∷ true ∷ .nil => rfl
  | false ∷ true ∷ true ∷ true ∷ .nil => rfl
  | false ∷ true ∷ false ∷ true ∷ .nil => rfl
  | true ∷ true ∷ false ∷ true ∷ .nil => rfl
  | true ∷ false ∷ false ∷ true ∷ .nil => rfl
  | false ∷ false ∷ false ∷ true ∷ .nil => rfl

end QCert.Alt16RevCir

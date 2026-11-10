/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The interpretation of circuits as even permutations

Translation of `Examples/Groups/Alternating/Interpretation.agda`:
`sem : Circ n → Alt n` (the Agda's `⟦_⟧`).

A generator denotes an even permutation (`semG`, the Agda's `⟦_⟧ᵍ`) and a
word the composite, read left to right: `w * v` applies `w` first, then `v`
(`sem_mul`).  `sem_up` (the Agda's `⟦↑⟧`) is the one computation law the
rest of the development needs: shifting a circuit shifts its denotation.

This says nothing about the relations.  That `sem` respects them is
`Soundness`.

**Deviations from the Agda.**  The Agda defines `⟦_⟧` by recursion on the
word, a tree, with `⟦ w • v ⟧ = ⟦ w ⟧ ∙ᴬ ⟦ v ⟧` by definition.  The
framework's words are lists, and `Alt n` is Mathlib's group, which
multiplies in operator order (the Agda's `a ∙ᴬ b` is `b * a`): `sem` is the
monoid homomorphism that the generators induce into the opposite group
(`semOp`, `FreeMonoid.lift`), read back, and the Agda's three clauses are
the lemmas `sem_of`, `sem_one`, `sem_mul` (pointwise, as the Agda's `≈ᴬ`;
`sem_one'` and `sem_mul'` state them in the group).  `semOp` and
`lift_semOp` are how `Presentation` states the theorem.
-/
import QCert.Alt16RevCir.Lib.Alternating.Semantics
import QCert.Alt16RevCir.Lib.Alternating.Syntactics
import Mathlib.Algebra.Group.Opposite

namespace QCert.Alt16RevCir.Alternating

open QCert QCert.Circuit

variable {n : ℕ}

/-! ## Denotation of generators and words -/

/-- The even permutation of a generator (the Agda's `⟦_⟧ᵍ`). -/
def semG : {n : ℕ} → Gn n → Alt n
  | _, .gate0 g => nomatch g
  | _, .gate1 g => nomatch g
  | _, .gate2 g => nomatch g
  | _, .gate3 .ω_gate => cycleA
  | _, .up g => shiftA (semG g)

theorem perm_semG_ω : Alt.perm (semG (Gen.gate3 Gate.ω_gate : Gn (n + 3))) = cycle := rfl

theorem perm_semG_up (g : Gn n) : Alt.perm (semG g.up) = lift₀ (Alt.perm (semG g)) := rfl

/-- The semantics of a generator in the Agda's (diagram-order) alternating
group, the opposite of Mathlib's. -/
def semOp (g : Gn n) : (Alt n)ᵐᵒᵖ := MulOpposite.op (semG g)

/-- The even permutation of a circuit (the Agda's `⟦_⟧`).  Words are read
left to right: `w * v` applies `w` first, then `v`. -/
def sem (w : Circ n) : Alt n := MulOpposite.unop (FreeMonoid.lift semOp w)

/-- A circuit's reading in the opposite group is `op` of its even
permutation. -/
theorem lift_semOp (w : Circ n) : FreeMonoid.lift semOp w = MulOpposite.op (sem w) := rfl

/-- `⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ`. -/
theorem sem_of (g : Gn n) : sem (FreeMonoid.of g) = semG g := by
  rw [sem, FreeMonoid.lift_eval_of]; rfl

/-- `⟦ ε ⟧ = εᴬ`. -/
theorem sem_one' : sem (1 : Circ n) = 1 := by
  rw [sem, map_one]; rfl

/-- `⟦ w • v ⟧ = ⟦ w ⟧ ∙ᴬ ⟦ v ⟧`, the product in diagram order. -/
theorem sem_mul' (w v : Circ n) : sem (w * v) = sem v * sem w := by
  rw [sem, map_mul]; rfl

theorem sem_one (i : Fin n) : Alt.perm (sem (1 : Circ n)) i = i := by
  rw [sem_one']; rfl

theorem sem_mul (w v : Circ n) (i : Fin n) :
    Alt.perm (sem (w * v)) i = Alt.perm (sem v) (Alt.perm (sem w) i) := by
  rw [sem_mul']; rfl

/-! ## Shifting -/

/-- `⟦ w ↑ ⟧` agrees with `lift₀ ⟦ w ⟧` pointwise (the Agda's `⟦↑⟧`). -/
theorem sem_up (w : Circ n) (k : Fin (n + 1)) :
    Alt.perm (sem (shift w)) k = lift₀ (Alt.perm (sem w)) k := by
  induction w using FreeMonoid.inductionOn' generalizing k with
  | one => rw [map_one, sem_one, sem_one', Alt.perm_one, lift₀_refl]
  | mul_of g w ih =>
    rw [map_mul, shift_of, sem_mul, sem_of, perm_semG_up, ih, sem_mul', sem_of, Alt.perm_mul,
      lift₀_trans]

end QCert.Alt16RevCir.Alternating

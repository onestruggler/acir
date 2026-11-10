/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Semantics of the alternating group: the even permutations of `Fin n`

Translation of `Examples/Groups/Alternating/Semantics.agda`.  A permutation
is even when it is a product of an even number of transpositions (Lafont,
Section 2.4), i.e. when its sign (`Parity`) is `false`.  `Alt n` is the type
of the even permutations of `n` points, a group under composition.

Nothing here mentions the syntax.  `cycle` and `shiftA` are named after the
generators they will interpret; the map from circuits to them is
`Interpretation`, and that it respects the relations is `Soundness`.

**Deviation from the Agda.**  `Alt n` is Mathlib's `alternatingGroup (Fin n)`
(as a type), with `Alt.perm` and `Alt.even` for the Agda record's fields and
`Alt.mk` for its constructor.  The Agda's `a ≈ᴬ b` (the permutations agree
pointwise) is stated pointwise where it occurs,
`∀ i, Alt.perm a i = Alt.perm b i`, and implies `a = b` (`Alt.ext`).  The
Agda's group `Alt-group n` (`_∙ᴬ_`, `εᴬ`, `_⁻¹ᴬ`, `Alt-isGroup`) composes in
diagram order (`∘ₚ`); Mathlib's group on `alternatingGroup` composes in
operator order (`(a * b) x = a (b x)`), so the Agda's `a ∙ᴬ b` is `b * a`
(`Alt.perm_mul`), `εᴬ` is `1` and `a ⁻¹ᴬ` is `a⁻¹`: the Agda's group is the
opposite of Mathlib's, and its laws are Mathlib's.  `cycle` is defined by
cases on the value of its argument, as the Agda's `cycle-to` and
`cycle-from`, and `cycle_val` states it without cases.
-/
import QCert.Alt16RevCir.Lib.Alternating.Parity

namespace QCert.Alt16RevCir.Alternating

open Symmetric

variable {n : ℕ}

/-! ## Even permutations -/

theorem sign_eq_false_iff_mem (π : Equiv.Perm (Fin n)) :
    sign π = false ↔ π ∈ alternatingGroup (Fin n) := by
  rw [sign_eq_false_iff, Equiv.Perm.mem_alternatingGroup]

/-- The even permutations of `n` points (the Agda's `Alt n`), Mathlib's
`alternatingGroup (Fin n)`. -/
abbrev Alt (n : ℕ) := ↥(alternatingGroup (Fin n))

/-- The permutation of an even permutation (the Agda's field `perm`). -/
def Alt.perm (a : Alt n) : Equiv.Perm (Fin n) := a.1

/-- It is even (the Agda's field `even`). -/
theorem Alt.even (a : Alt n) : sign (Alt.perm a) = false :=
  (sign_eq_false_iff_mem _).2 a.2

/-- An even permutation (the Agda's record constructor). -/
def Alt.mk (π : Equiv.Perm (Fin n)) (h : sign π = false) : Alt n :=
  ⟨π, (sign_eq_false_iff_mem π).1 h⟩

@[simp] theorem Alt.perm_mk (π : Equiv.Perm (Fin n)) (h : sign π = false) :
    Alt.perm (Alt.mk π h) = π := rfl

theorem Alt.ext {a b : Alt n} (h : ∀ i, Alt.perm a i = Alt.perm b i) : a = b :=
  Subtype.ext (Equiv.ext h)

/-! ## The group `𝔄ₙ` -/

/-- Mathlib's multiplication is in operator order: the Agda's `a ∙ᴬ b`
(diagram order) is `b * a`. -/
theorem Alt.perm_mul (a b : Alt n) : Alt.perm (a * b) = (Alt.perm b).trans (Alt.perm a) := rfl

@[simp] theorem Alt.perm_one : Alt.perm (1 : Alt n) = Equiv.refl _ := rfl

theorem Alt.perm_inv (a : Alt n) : Alt.perm a⁻¹ = (Alt.perm a).symm := rfl

/-! ## Semantic building blocks -/

/-- The Agda's `cycle-to`. -/
private def cycleTo : Fin (n + 3) → Fin (n + 3)
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨1, _⟩ => ⟨2, by omega⟩
  | ⟨2, _⟩ => ⟨0, by omega⟩
  | ⟨k + 3, h⟩ => ⟨k + 3, h⟩

/-- The Agda's `cycle-from`. -/
private def cycleFrom : Fin (n + 3) → Fin (n + 3)
  | ⟨0, _⟩ => ⟨2, by omega⟩
  | ⟨1, _⟩ => ⟨0, by omega⟩
  | ⟨2, _⟩ => ⟨1, by omega⟩
  | ⟨k + 3, h⟩ => ⟨k + 3, h⟩

/-- The cyclic permutation of the wires `0 1 2`, sending `0` to `1`, `1` to
`2` and `2` to `0`: what `ω` will denote. -/
def cycle : Equiv.Perm (Fin (n + 3)) where
  toFun := cycleTo
  invFun := cycleFrom
  left_inv
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨_ + 3, _⟩ => rfl
  right_inv
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨_ + 3, _⟩ => rfl

theorem cycle_val : ∀ i : Fin (n + 3),
    (cycle i).val =
      if i.val = 0 then 1 else if i.val = 1 then 2 else if i.val = 2 then 0 else i.val
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨k + 3, _⟩ => by
    show k + 3 = _
    simp

/-- It is two transpositions: the swap of the wires `1 2`, then that of the
wires `0 1` (the picture defining `ω` on p. 267). -/
theorem cycle_even : sign (cycle (n := n)) = false := by
  have q₁ : 2 + 1 ≤ n + 3 := by omega
  have q₀ : 2 + 0 ≤ n + 3 := by omega
  rw [sign_of (s 1 q₁ * s 0 q₀) cycle, parity_mul, parity_of, parity_of]
  · rfl
  · intro k
    apply Fin.ext
    rw [perm_mul_apply, perm_of, perm_of, cycle_val]
    simp only [swp]
    unfold ToffoliHadamardRS.CoxeterFrames.sw
    obtain ⟨k, hk⟩ := k
    rcases k with _ | _ | _ | j <;> simp

/-- The Agda's `cycleᴬ`. -/
def cycleA : Alt (n + 3) := Alt.mk cycle cycle_even

@[simp] theorem perm_cycleA : Alt.perm (cycleA (n := n)) = cycle := rfl

/-- Shift a permutation up by one wire: what `Gen.up` will act as (the
Agda's `shiftᴬ`). -/
def shiftA (a : Alt n) : Alt (n + 1) :=
  Alt.mk (lift₀ (Alt.perm a)) ((sign_lift₀ (Alt.perm a)).trans (Alt.even a))

@[simp] theorem perm_shiftA (a : Alt n) : Alt.perm (shiftA a) = lift₀ (Alt.perm a) := rfl

end QCert.Alt16RevCir.Alternating

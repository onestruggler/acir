/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Parity of words, signs of permutations, and the even permutations

Translation of what `Examples/Groups/XCXCCX-4bit` uses of the Agda library
`Examples/Groups/Alternating` (`Parity`, `Semantics`): the parity of a word
(`parity`, whether its length is odd), the sign of a permutation as a
Boolean (`sign`, `true` for odd), the sign of a word's permutation is the
word's parity (`sign_of`), the laws of signs (`sign_cong`, `sign_comp`,
`sign_id`, `sign_flip`), and the even permutations `Alt n`.

**Deviation from the Agda.**  The Agda defines the sign of `π` as the parity
of Symmetric's word for `π` and derives its laws from the completeness of
Symmetric's presentation (Lafont's Theorem 1).  Here the sign is Mathlib's
`Equiv.Perm.sign` read as a Boolean (`sign π = true ↔ Equiv.Perm.sign π = -1`),
whose laws are Mathlib's; `sign_of` is proved from the letters being
transpositions (`perm_of_eq_swap`).  `Alt n` is Mathlib's
`alternatingGroup (Fin n)` (as a type), with `Alt.perm` and `Alt.even` for the
Agda record's fields and `Alt.mk` for its constructor.  The Agda's group
`Alt-group n` composes in diagram order (`∘ₚ`); Mathlib's group on
`alternatingGroup` composes in operator order (`(a * b) x = a (b x)`), so the
Agda's `a ∙ᴬ b` is `b * a`.  Nothing here should be evaluated on a numeral
permutation: `Equiv.Perm.sign` is not meant for the kernel (the Agda README's
trap about evaluating signs at numeral widths); go through `sign_of`.
-/
import QCert.XCXCCX4bit.Lib.Symmetric
import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace QCert.XCXCCX4bit.Alternating

open Symmetric

variable {n : ℕ}

/-! ## The parity of a word -/

/-- Whether the length of a word is odd (the Agda's `parity`). -/
def parity {A : Type*} (w : Word A) : Bool := decide (FreeMonoid.length w % 2 = 1)

section Parity

variable {A : Type*}

@[simp] theorem parity_one : parity (1 : Word A) = false := rfl

@[simp] theorem parity_of (a : A) : parity (FreeMonoid.of a) = true := rfl

theorem parity_mul (w v : Word A) : parity (w * v) = (parity w ^^ parity v) := by
  unfold parity
  rw [FreeMonoid.length_mul]
  rcases Nat.mod_two_eq_zero_or_one (FreeMonoid.length w) with h | h <;>
  rcases Nat.mod_two_eq_zero_or_one (FreeMonoid.length v) with h' | h' <;>
  simp [h, h', Nat.add_mod]

/-- The Agda's `parity-wmap`. -/
theorem parity_map {B : Type*} (f : A → B) (w : Word A) :
    parity (FreeMonoid.map f w) = parity w := by
  unfold parity FreeMonoid.length
  rw [FreeMonoid.toList_map, List.length_map]

end Parity

/-! ## The sign of a permutation -/

/-- The sign of a permutation as a Boolean, `true` for an odd one (the
Agda's `sign`). -/
def sign (π : Equiv.Perm (Fin n)) : Bool := decide (Equiv.Perm.sign π = -1)

theorem sign_eq_true_iff (π : Equiv.Perm (Fin n)) : sign π = true ↔ Equiv.Perm.sign π = -1 := by
  simp [sign]

theorem sign_eq_false_iff (π : Equiv.Perm (Fin n)) : sign π = false ↔ Equiv.Perm.sign π = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [sign, h]

/-- Mathlib's sign from the Boolean one. -/
theorem sign_units (π : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign π = if sign π then -1 else 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [sign, h]

/-- A letter denotes a transposition. -/
theorem perm_of_eq_swap (g : SG n) :
    perm (FreeMonoid.of g) = Equiv.swap ⟨g.1, by have := g.2; omega⟩ ⟨g.1 + 1, by have := g.2; omega⟩ := by
  ext x
  rw [perm_of, Equiv.swap_apply_def]
  simp only [swp, Fin.ext_iff]
  unfold ToffoliHadamardRS.CoxeterFrames.sw
  split_ifs <;> simp_all

/-- The sign of a composite (the Agda's `sign-∘`; its `π ∘ₚ ρ` is
`π.trans ρ`). -/
theorem sign_comp (π ρ : Equiv.Perm (Fin n)) : sign (π.trans ρ) = (sign π ^^ sign ρ) := by
  have e : Equiv.Perm.sign (π.trans ρ) = Equiv.Perm.sign π * Equiv.Perm.sign ρ := by
    rw [← Equiv.Perm.mul_def, Equiv.Perm.sign_mul, mul_comm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;>
  rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h' | h' <;>
  simp [sign, e, h, h']

/-- A letter is odd. -/
theorem sign_letter (g : SG n) : sign (perm (FreeMonoid.of g)) = true := by
  rw [sign_eq_true_iff, perm_of_eq_swap, Equiv.Perm.sign_swap (by simp [Fin.ext_iff])]

/-- The sign of a word's permutation is its parity. -/
theorem sign_perm (w : Word (SG n)) : sign (perm w) = parity w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [perm_one, parity_one]; simp [sign]
  | mul_of g w ih => rw [perm_mul, sign_comp, ih, sign_letter, parity_mul, parity_of]

/-- Every word realising `π` has the parity of its sign (the Agda's
`sign-of`). -/
theorem sign_of (w : Word (SG n)) (π : Equiv.Perm (Fin n)) (h : ∀ k, perm w k = π k) :
    sign π = parity w := by
  rw [← Equiv.ext h, sign_perm]

/-- The Agda's `sign-cong`. -/
theorem sign_cong {π ρ : Equiv.Perm (Fin n)} (h : ∀ k, π k = ρ k) : sign π = sign ρ := by
  rw [Equiv.ext h]

/-- The Agda's `sign-id`. -/
@[simp] theorem sign_id : sign (Equiv.refl (Fin n)) = false := by
  simp [sign, ← Equiv.Perm.one_def]

@[simp] theorem sign_one : sign (1 : Equiv.Perm (Fin n)) = false := sign_id

/-- The Agda's `sign-flip`. -/
@[simp] theorem sign_flip (π : Equiv.Perm (Fin n)) : sign π.symm = sign π := by
  simp [sign]

/-! ## The even permutations -/

theorem sign_eq_false_iff_mem (π : Equiv.Perm (Fin n)) :
    sign π = false ↔ π ∈ alternatingGroup (Fin n) := by
  rw [sign_eq_false_iff, Equiv.Perm.mem_alternatingGroup]

/-- The even permutations of `n` states (the Agda's `Alt n`), Mathlib's
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

/-- Mathlib's multiplication is in operator order: the Agda's `a ∙ᴬ b`
(diagram order) is `b * a`. -/
theorem Alt.perm_mul (a b : Alt n) : Alt.perm (a * b) = (Alt.perm b).trans (Alt.perm a) := rfl

@[simp] theorem Alt.perm_one : Alt.perm (1 : Alt n) = Equiv.refl _ := rfl

theorem Alt.perm_inv (a : Alt n) : Alt.perm a⁻¹ = (Alt.perm a).symm := rfl

end QCert.XCXCCX4bit.Alternating

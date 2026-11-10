/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The sign of a permutation

Translation of `Examples/Groups/Alternating/Parity.agda`: the parity of a
word (`parity`, whether its length is odd), the sign of a permutation as a
Boolean (`sign`, `true` for odd), every word of adjacent transpositions
realising a permutation has the parity of its sign (`sign_of`), and the laws
of signs (`sign_cong`, `sign_comp`, `sign_id`, `sign_flip`, `sign_lift₀`).

Lafont calls a permutation even when it is a product of an even number of
transpositions.  The words of `Symmetric` are products of adjacent
transpositions, so the sign of a permutation is the parity of any word
realising it.

**Deviation from the Agda.**  The Agda defines the sign of `π` as the parity
of Symmetric's word for `π` and derives its laws from the completeness of
Symmetric's presentation (Lafont's Theorem 1), through `parity-sound`.
Here the sign is Mathlib's `Equiv.Perm.sign` read as a Boolean
(`sign π = true ↔ Equiv.Perm.sign π = -1`), whose laws are Mathlib's;
`sign_of` is proved from the letters being transpositions
(`perm_of_eq_swap`).  `parity_ax` and `parity_sound` are translated, for
the relations `SymRel` of the Lean `Symmetric`, but nothing uses them.  The
parity of a word is that of its length (the Agda's words are trees, and its
`parity` a recursion on them; `parity_one`, `parity_of`, `parity_mul` are
its clauses).

Permutations are Mathlib's `Equiv.Perm (Fin n)`: the Agda's `π ⟨$⟩ʳ i` is
`π i`, `π ⟨$⟩ˡ i` is `π.symm i`, `π ∘ₚ ρ` (diagram order) is `π.trans ρ` and
`flip π` is `π.symm`.  The standard library's `lift₀` (a permutation one
wire up, fixing `0`) and `remove zero` (its inverse on the permutations
that fix `0`), with the lemmas the development uses (`lift₀-id`,
`lift₀-comp`, `lift₀-cong`, `lift₀-remove`), are defined here: `lift₀` by
cases as in the standard library, `remove₀` as the second component of
Mathlib's `Equiv.Perm.decomposeFin`.  `sign_lift₀` is Mathlib's
`Equiv.Perm.decomposeFin.symm_sign`, where the Agda shifts Symmetric's word
for `π`.

Nothing here should be evaluated on a numeral permutation:
`Equiv.Perm.sign` is not meant for the kernel; go through `sign_of`.
-/
import QCert.Alt16RevCir.Lib.Symmetric
import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace QCert.Alt16RevCir.Alternating

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

/-! ## Congruent words of transpositions have the same parity -/

/-- The Agda's `parity-ax`: the two sides of a relation of `Symmetric` have
the same parity. -/
theorem parity_ax {w v : Word (SG n)} (h : SymRel n w v) : parity w = parity v := by
  cases h <;> simp [parity_mul]

/-- The Agda's `parity-sound`. -/
theorem parity_sound {w v : Word (SG n)} (d : Derivable (SymRel n) w v) :
    parity w = parity v := by
  let c : Con (Word (SG n)) :=
    { r := fun w v => parity w = parity v
      iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
      mul' := fun {w w' v v'} e e' => by rw [parity_mul, parity_mul, e, e'] }
  have : conGen (SymRel n) ≤ c := Con.conGen_le fun _ _ r => parity_ax r
  exact this d

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
    perm (FreeMonoid.of g) =
      Equiv.swap ⟨g.1, by have := g.2; omega⟩ ⟨g.1 + 1, by have := g.2; omega⟩ := by
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

/-! ## A permutation one wire up -/

/-- `π` on the wires `1, …, n` of `n + 1` wires, wire `0` fixed (the
standard library's `lift₀`). -/
def lift₀ (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun
    | ⟨0, _⟩ => 0
    | ⟨k + 1, h⟩ => (π ⟨k, Nat.lt_of_succ_lt_succ h⟩).succ
  invFun
    | ⟨0, _⟩ => 0
    | ⟨k + 1, h⟩ => (π.symm ⟨k, Nat.lt_of_succ_lt_succ h⟩).succ
  left_inv
    | ⟨0, _⟩ => rfl
    | ⟨k + 1, h⟩ => by
      show (π.symm (π ⟨k, _⟩)).succ = _
      rw [Equiv.symm_apply_apply]; rfl
  right_inv
    | ⟨0, _⟩ => rfl
    | ⟨k + 1, h⟩ => by
      show (π (π.symm ⟨k, _⟩)).succ = _
      rw [Equiv.apply_symm_apply]; rfl

@[simp] theorem lift₀_zero (π : Equiv.Perm (Fin n)) : lift₀ π 0 = 0 := rfl

@[simp] theorem lift₀_succ (π : Equiv.Perm (Fin n)) (j : Fin n) :
    lift₀ π j.succ = (π j).succ := rfl

theorem lift₀_symm (π : Equiv.Perm (Fin n)) : (lift₀ π).symm = lift₀ π.symm := rfl

/-- The standard library's `lift₀-id`. -/
theorem lift₀_refl (k : Fin (n + 1)) : lift₀ (Equiv.refl (Fin n)) k = k := by
  cases k using Fin.cases with
  | zero => rfl
  | succ j => rfl

/-- The standard library's `lift₀-comp`. -/
theorem lift₀_trans (π ρ : Equiv.Perm (Fin n)) (k : Fin (n + 1)) :
    lift₀ (π.trans ρ) k = lift₀ ρ (lift₀ π k) := by
  cases k using Fin.cases with
  | zero => rfl
  | succ j => rfl

/-- The standard library's `lift₀-cong`. -/
theorem lift₀_cong {π ρ : Equiv.Perm (Fin n)} (h : ∀ k, π k = ρ k) (k : Fin (n + 1)) :
    lift₀ π k = lift₀ ρ k := by
  rw [Equiv.ext h]

theorem lift₀_eq_decomposeFin (π : Equiv.Perm (Fin n)) :
    lift₀ π = Equiv.Perm.decomposeFin.symm (0, π) := by
  ext k
  cases k using Fin.cases with
  | zero => rw [Equiv.Perm.decomposeFin_symm_apply_zero]; rfl
  | succ j => rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]; rfl

/-- The Agda's `sign-lift₀`. -/
theorem sign_lift₀ (π : Equiv.Perm (Fin n)) : sign (lift₀ π) = sign π := by
  unfold sign
  rw [lift₀_eq_decomposeFin, Equiv.Perm.decomposeFin.symm_sign]
  simp

/-- A permutation of `n + 1` wires with wire `0` removed (the standard
library's `remove zero`). -/
def remove₀ (χ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin n) :=
  (Equiv.Perm.decomposeFin χ).2

/-- The standard library's `lift₀-remove`: a permutation that fixes wire `0`
is the lift of what it does above it. -/
theorem lift₀_remove₀ (χ : Equiv.Perm (Fin (n + 1))) (h : χ 0 = 0) (k : Fin (n + 1)) :
    lift₀ (remove₀ χ) k = χ k := by
  have e : Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin χ) = χ :=
    Equiv.symm_apply_apply _ χ
  unfold remove₀
  generalize Equiv.Perm.decomposeFin χ = d at e ⊢
  obtain ⟨p, ρ⟩ := d
  have hp : p = 0 := by
    have := Equiv.Perm.decomposeFin_symm_apply_zero p ρ
    rw [e, h] at this
    exact this.symm
  subst hp
  rw [lift₀_eq_decomposeFin, e]

end QCert.Alt16RevCir.Alternating

/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lafont's Lemma 6, existence

Translation of `Examples/Groups/Alternating/Surjectivity.agda`: every even
permutation is the denotation of a canonical form.

By induction on the width, as in the paper.  Given an even `π` on `n + 1`
wires, the stairs `c` whose target is `π 0` represents `π`'s coset: dividing
`sem (sec c)` out of `π` fixes wire 0 and leaves an even permutation, which
with wire 0 removed is the denotation of a canonical form one wire narrower.
On two wires there is only the empty stairs, and there an even permutation
fixes wire 0, the swap being a single transposition.

This mentions no relation.  `surjective` packages it, for any sound theory,
as the surjectivity that promotes a sub-presentation to a presentation.

**Deviations from the Agda.**  `coset_of` and `canonical` return subtypes
(the Agda's `∃`).  The swap of two wires is Symmetric's letter `s 0`.  The
Agda's `remove zero χ` and `lift₀-remove` are `remove₀ χ` and
`lift₀_remove₀` of `Parity`.  The Agda's `a ∙ᴬ ⟦ [ c ]ᶜ ⟧ ⁻¹ᴬ` (diagram
order) is `(sem (sec c))⁻¹ * a` in Mathlib's group.  `surjective` is stated
as the Agda's standard library states `Surjective` for setoids: every
circuit congruent to the canonical form denotes the permutation.
-/
import QCert.Alt16RevCir.Lib.Alternating.UniqueNormalForm

namespace QCert.Alt16RevCir.Alternating

open QCert QCert.Circuit

variable {n : ℕ}

/-! ## The stairs of an even permutation -/

/-- In `Fin 2`, what is not `1` is `0`. -/
private theorem not_one : ∀ j : Fin 2, j ≠ 1 → j = 0 := by decide

/-- An even permutation of two wires fixes wire 0: sending it to wire 1 it
would be the swap, a single transposition. -/
theorem fixes_zero (a : Alt 2) : 0 = Alt.perm a 0 := by
  have by_cases : ∀ j : Fin 2, Alt.perm a 0 = j → 0 = Alt.perm a 0 := by
    intro j e
    match j, e with
    | ⟨0, _⟩, e => exact e.symm
    | ⟨1, _⟩, e =>
      have π₁ : Alt.perm a 1 = 0 := not_one _ fun e' =>
        absurd (perm_injective _ (e'.trans e.symm)) (by decide)
      have swap : ∀ k, Symmetric.perm (Symmetric.s 0 (Nat.le_refl 2)) k = Alt.perm a k := by
        intro k
        rw [Symmetric.perm_of]
        match k with
        | ⟨0, _⟩ => exact e.symm
        | ⟨1, _⟩ => exact π₁.symm
      exact absurd ((sign_of _ _ swap).symm.trans (Alt.even a)) (by decide)
  exact by_cases _ rfl

/-- `Fin 1` has only `0`. -/
private theorem only : ∀ j : Fin 1, 0 = j := by decide

/-- The stairs whose target is where an even permutation sends wire 0. -/
def coset_of : {n : ℕ} → (a : Alt (n + 1)) → {c : C n // target c = Alt.perm a 0}
  | 0, a => ⟨.ε, only (Alt.perm a 0)⟩
  | 1, a => ⟨.ε, fixes_zero a⟩
  | _ + 2, a => ⟨coset (Alt.perm a 0), target_coset _⟩

/-! ## Every even permutation is a canonical form -/

/-- A canonical form for each even permutation. -/
def canonical : (n : ℕ) → (a : Alt n) →
    {x : NF n // ∀ i, Alt.perm (sem (inv_nf x)) i = Alt.perm a i}
  | 0, _ => ⟨(), fun i => i.elim0⟩
  | n + 1, a =>
    let c := (coset_of a).1
    let ρ := Alt.perm (sem (sec c))
    have ρ₀ : ρ 0 = Alt.perm a 0 := (sem_sec_zero c).trans (coset_of a).2
    -- `π` with the stairs divided out fixes wire 0, and it is even.
    let χ := (Alt.perm a).trans ρ.symm
    have χ₀ : χ 0 = 0 := by
      show ρ.symm (Alt.perm a 0) = 0
      rw [← ρ₀, Equiv.symm_apply_apply]
    have χ_even : sign χ = false := Alt.even ((sem (sec c))⁻¹ * a)
    -- So it is a permutation of the top wires, shifted.
    let ρ' := remove₀ χ
    have ρ'_even : sign ρ' = false :=
      (sign_lift₀ ρ').symm.trans ((sign_cong (lift₀_remove₀ χ χ₀)).trans χ_even)
    let r := canonical n (Alt.mk ρ' ρ'_even)
    ⟨(r.1, c), fun k => by
      rw [inv_nf_succ, sem_mul, sem_up, lift₀_cong r.2 k, Alt.perm_mk, lift₀_remove₀ χ χ₀ k]
      exact Equiv.apply_symm_apply ρ _⟩

/-! ## Surjectivity of `sem` -/

/-- The canonical form realising `a`, packaged as surjectivity: by
soundness, any circuit congruent to it denotes `a`. -/
theorem surjective {T : Theory}
    (sound : ∀ {n : ℕ} {w v : Circ n}, Derives T n w v →
      ∀ i, Alt.perm (sem w) i = Alt.perm (sem v) i)
    (a : Alt n) :
    ∃ w : Circ n, ∀ z : Circ n, Derives T n z w → ∀ k, Alt.perm (sem z) k = Alt.perm a k :=
  ⟨inv_nf (canonical n a).1, fun _ d k => (sound d k).trans ((canonical n a).2 k)⟩

end QCert.Alt16RevCir.Alternating

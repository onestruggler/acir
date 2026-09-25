------------------------------------------------------------------------
-- Presentations of groups
--
-- Unitary path-sums: orthonormal columns and orthonormal rows
--
-- PathSum.PartialIsometry states definition 2.4 on the unnormalised
-- operator Ũ = √2^k · U_ξ, whose entry at output z and input x is
-- amp ξ x z: Isometric ξ says U†U = I, the columns of U_ξ orthonormal.
-- A unitary is an isometry whose adjoint is one too, UU† = I, the rows
-- orthonormal as well.  That second half is stated here in the same
-- way, with the denominators cleared:
--
--   cogram ξ z z′ = Σ_x amp ξ x z · conj (amp ξ x z′)
--
-- is the entry of ŨŨ† at (z , z′) -- not transposed, unlike
-- PathSum.PartialIsometry's gram -- and Coisometric ξ asks that it be
-- 2^k [z = z′], which is UU† = I.  Unitary ξ is the pair.
--
-- For a square matrix over a field either half implies the other, by
-- linear algebra that is not formalised here; so Unitary asks for both,
-- and a path-sum is called unitary only where both are proved.  (The
-- circuits of PathSum.Unitarity and PathSum.CRK.Unitarity are unitary:
-- there UU† = I comes from the circuit itself, its matrix transposed
-- being that of the circuit reversed.)
--
-- As for Isometric, clearing the denominators loses nothing: path-sums
-- with the same operator have proportional cogram matrices (cogram-≋),
-- so Coisometric and Unitary are invariant under ≋ and are properties
-- of U_ξ, not of the way ξ writes it.  A unitary path-sum is in
-- particular an isometry, so it is well-formed in the sense of
-- definition 2.4, satisfies PathSum.Isometry's WellFormed, and lemma
-- 4.1 applies to it (lemma-4-1-unitary).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; _^_)

module PathSum.PartialIsometry.Unitary (M₀ : ℕ) where

open import Data.Integer.Base using (ℤ; +_; _*_)
open import Data.Integer.Properties using (*-cancelˡ-≡)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import PathSum.Assign using (same)
open import PathSum.Base using (PathSum; idPS)
open import PathSum.Cyclotomic M₀ using (Amp; _≐_; _·ᴬ_; scale)
open import PathSum.Denotation M₀ using (Assign; amp; _≋_)
open import PathSum.Hermitian M₀ using
  ([_]ᴬ; inner; inner-cong; inner-scale)
open import PathSum.Isometry M₀ using (WellFormed; Restriction-id)
open import PathSum.PartialIsometry M₀ using
  (Isometric; PartialIsometric; Isometric⇒PartialIsometric;
   Isometric⇒WellFormed; lemma-4-1-isometric; Isometric-≋)

import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; _:*_; _:=_)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- The rows of the operator

-- The Hermitian product of the rows at z and z′: the entry of ŨŨ† at
-- (z , z′).

cogram : PathSum n k m → Assign n → Assign n → Amp
cogram ξ z z′ = inner (λ x → amp ξ x z) (λ x → amp ξ x z′)

-- UU† = I, with denominators cleared.

Coisometric : PathSum n k m → Set
Coisometric {n = n} {k = k} ξ =
  ∀ (z z′ : Assign n) → cogram ξ z z′ ≐ (+ (2 ^ k)) ·ᴬ [ same z z′ ]ᴬ

-- Unitary: U†U = I and UU† = I.  (A conjunction rather than a record:
-- declaring a record whose fields are these types costs Agda some 13 s
-- and 3.7 GB, the product nothing.)

Unitary : PathSum n k m → Set
Unitary ξ = Isometric ξ × Coisometric ξ

Unitary⇒Isometric : (ξ : PathSum n k m) → Unitary ξ → Isometric ξ
Unitary⇒Isometric ξ = proj₁

Unitary⇒Coisometric : (ξ : PathSum n k m) → Unitary ξ → Coisometric ξ
Unitary⇒Coisometric ξ = proj₂


------------------------------------------------------------------------
-- A unitary is well-formed

-- It is an isometry, so definition 2.4, WellFormed and lemma 4.1 all
-- apply.

Unitary⇒PartialIsometric : (ξ : PathSum n k m) → Unitary ξ →
                           PartialIsometric ξ
Unitary⇒PartialIsometric ξ u =
  Isometric⇒PartialIsometric ξ (Unitary⇒Isometric ξ u)

Unitary⇒WellFormed : (ξ : PathSum n k m) → Unitary ξ → WellFormed ξ
Unitary⇒WellFormed ξ u = Isometric⇒WellFormed ξ (Unitary⇒Isometric ξ u)

lemma-4-1-unitary : (ξ : PathSum n k m) → Unitary ξ →
                    (ξ ≋ idPS ⇔ Restriction-id ξ)
lemma-4-1-unitary ξ u = lemma-4-1-isometric ξ (Unitary⇒Isometric ξ u)


------------------------------------------------------------------------
-- Unitarity is a property of the operator

-- ξ ≋ ζ says √2^k′ · amp ξ = √2^k · amp ζ entrywise, and normalising
-- both rows by √2^j multiplies their product by 2^j (inner-scale), so
-- equivalent path-sums have proportional cogram matrices, and the
-- powers of 2 cancel -- exactly as for Isometric (Isometric-≋).

cogram-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) → ξ ≋ ζ →
           ∀ z z′ →
           (+ (2 ^ k′)) ·ᴬ cogram ξ z z′ ≐ (+ (2 ^ k)) ·ᴬ cogram ζ z z′
cogram-≋ {k = k} {k′ = k′} ξ ζ eq z z′ i =
  trans (sym (inner-scale k′ (λ x → amp ξ x z) (λ x → amp ξ x z′) i))
    (trans (inner-cong {ψ = λ x → scale k′ (amp ξ x z)}
                       {ψ′ = λ x → scale k (amp ζ x z)}
                       {φ = λ x → scale k′ (amp ξ x z′)}
                       {φ′ = λ x → scale k (amp ζ x z′)}
                       (λ x → eq x z) (λ x → eq x z′) i)
           (inner-scale k (λ x → amp ζ x z) (λ x → amp ζ x z′) i))

private
  cancel : ∀ j {s t : ℤ} → (+ (2 ^ j)) * s ≡ (+ (2 ^ j)) * t → s ≡ t
  cancel j {s} {t} = *-cancelˡ-≡ (+ (2 ^ j)) s t {{ℕ.m^n≢0 2 j}}

  swap : ∀ p q t → p * (q * t) ≡ q * (p * t)
  swap = solve 3 (λ p q t → p :* (q :* t) := q :* (p :* t)) refl

Coisometric-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) → ξ ≋ ζ →
                Coisometric ξ → Coisometric ζ
Coisometric-≋ {k = k} {k′ = k′} ξ ζ eq co z z′ i = cancel k
  (trans (sym (cogram-≋ ξ ζ eq z z′ i))
    (trans (cong (λ t → (+ (2 ^ k′)) * t) (co z z′ i))
           (swap (+ (2 ^ k′)) (+ (2 ^ k)) ([ same z z′ ]ᴬ i))))

Unitary-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) → ξ ≋ ζ →
            Unitary ξ → Unitary ζ
Unitary-≋ ξ ζ eq (iso , co) =
  Isometric-≋ ξ ζ eq iso , Coisometric-≋ ξ ζ eq co

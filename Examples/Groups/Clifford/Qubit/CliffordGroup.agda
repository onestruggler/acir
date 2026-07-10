------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-qubit Clifford group (p = 2), non-split, as a concrete group.
--
-- Elements are Clifford words (over the gate generators Gen n) identified
-- when they act equally on the phased Pauli group P4 n by conjugation:
--
--     w ≈ᶜ v   ⟺   ∀ x → cact w x ≡ cact v x.
--
-- Since cact w faithfully represents the phaseless Clifford operator of w,
-- this quotient is exactly the phaseless Clifford group — the non-split
-- extension of Sp(2n,2) by the Pauli group.  Composition is word
-- concatenation (cact (w • v) = cact w ∘ cact v); the monoid laws are
-- near-definitional.  Inverses use the P4-order of each generator (S⁴ = H⁴
-- = CZ⁴ = 1 on P4) and are added in a later section.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Examples.Groups.Clifford.Qubit.CliffordGroup where

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Relation.Nullary.Decidable using (from-yes)
open import Algebra.Bundles using (Monoid)
open import Algebra.Structures using (IsMonoid ; IsSemigroup ; IsMagma)
open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open import Examples.Groups.Symplectic.Symplectic-Derived p-2 p-prime
  using (module Symplectic-Derived-Gen)
open Symplectic-Derived-Gen using (Gen)

open import Examples.Groups.Clifford.Qubit.SignedPauli using (P4Carrier)
open import Examples.Groups.Clifford.Qubit.CliffordAction using (cact)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Equality: equal action on P4

infix 4 _≈ᶜ_
_≈ᶜ_ : ∀ {n} → Word (Gen n) → Word (Gen n) → Set
_≈ᶜ_ {n} w v = (x : P4Carrier n) → cact w x ≡ cact v x

≈ᶜ-refl : {w : Word (Gen n)} → w ≈ᶜ w
≈ᶜ-refl x = Eq.refl

≈ᶜ-sym : {w v : Word (Gen n)} → w ≈ᶜ v → v ≈ᶜ w
≈ᶜ-sym w≈v x = Eq.sym (w≈v x)

≈ᶜ-trans : {w v u : Word (Gen n)} → w ≈ᶜ v → v ≈ᶜ u → w ≈ᶜ u
≈ᶜ-trans w≈v v≈u x = Eq.trans (w≈v x) (v≈u x)

≈ᶜ-isEquivalence : ∀ {n} → IsEquivalence (_≈ᶜ_ {n})
≈ᶜ-isEquivalence = record
  { refl  = λ {w}          → ≈ᶜ-refl {w = w}
  ; sym   = λ {w} {v}      → ≈ᶜ-sym {w = w} {v = v}
  ; trans = λ {w} {v} {u}  → ≈ᶜ-trans {w = w} {v = v} {u = u}
  }

------------------------------------------------------------------------
-- Monoid structure: concatenation of Clifford words
--
-- cact (w • v) = cact w ∘ cact v (word-act), so the magma/semigroup/monoid
-- laws all hold pointwise by computation.

∙-congᶜ : {w w' v v' : Word (Gen n)} → w ≈ᶜ w' → v ≈ᶜ v' → (w • v) ≈ᶜ (w' • v')
∙-congᶜ {w = w} {w'} {v} {v'} w≈w' v≈v' x =
  Eq.trans (Eq.cong (cact w) (v≈v' x)) (w≈w' (cact v' x))

assocᶜ : (w v u : Word (Gen n)) → ((w • v) • u) ≈ᶜ (w • (v • u))
assocᶜ w v u x = Eq.refl

identityˡᶜ : (w : Word (Gen n)) → (ε • w) ≈ᶜ w
identityˡᶜ w x = Eq.refl

identityʳᶜ : (w : Word (Gen n)) → (w • ε) ≈ᶜ w
identityʳᶜ w x = Eq.refl

isMonoidᶜ : ∀ {n} → IsMonoid (_≈ᶜ_ {n}) _•_ ε
isMonoidᶜ {n} = record
  { isSemigroup = record
    { isMagma = record
      { isEquivalence = ≈ᶜ-isEquivalence {n}
      ; ∙-cong        = λ {w} {w'} {v} {v'} → ∙-congᶜ {n} {w} {w'} {v} {v'}
      }
    ; assoc = assocᶜ
    }
  ; identity = identityˡᶜ , identityʳᶜ
  }
  where open import Data.Product using (_,_)

Clifford-monoid : ℕ → Monoid 0ℓ 0ℓ
Clifford-monoid n = record { isMonoid = isMonoidᶜ {n} }

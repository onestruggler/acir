------------------------------------------------------------------------
-- The Agda standard library
--
-- Right actions of ℕ-indexed families of monoids and groups on
-- vectors: the monoid at index n acts on length-n vectors over a
-- fixed setoid of objects, with pointwise equality.
--
-- Typical instances are width-indexed symmetry groups: the
-- permutation group at n acting on Vec ⊤ n by reindexing, or a
-- semantic group family (such as the symplectic groups) acting on
-- vectors of single-wire states (Vec Pauli₁ n).
--
-- (Staged in ForStdlib for upstreaming into Algebra.Action.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Algebra.IndexedAction where

open import Algebra.Bundles using (RawMonoid; Group)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec)
import Data.Vec.Relation.Binary.Equality.Setoid as VecEq
open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)

import ForStdlib.Algebra.Action as Action
open Action using (RightAction)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Indexed right actions

-- A right action of the family M of monoids on vectors over S: at
-- each index n, M n acts on Vec (Setoid.Carrier S) n up to pointwise
-- equality.  The laws are those of RightAction, stated uniformly in
-- the index.

record IndexedRightAction (M : ℕ → RawMonoid b ℓ₂) (S : Setoid a ℓ₁) :
                          Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  private
    module M (n : ℕ) = RawMonoid (M n)
    module S = Setoid S
  open VecEq S using (_≋_; ≋-setoid)

  infixl 7 _◁_
  field
    _◁_        : ∀ {n} → Vec S.Carrier n → M.Carrier n → Vec S.Carrier n
    ◁-cong     : ∀ {n} {xs xs′ : Vec S.Carrier n} {g g′ : M.Carrier n} →
                 xs ≋ xs′ → M._≈_ n g g′ → xs ◁ g ≋ xs′ ◁ g′
    ◁-identity : ∀ {n} (xs : Vec S.Carrier n) → xs ◁ M.ε n ≋ xs
    ◁-compose  : ∀ {n} (xs : Vec S.Carrier n) (g h : M.Carrier n) →
                 xs ◁ (M._∙_ n g h) ≋ (xs ◁ g) ◁ h

  -- At each index the action packages as a plain right action on the
  -- setoid of length-n vectors.
  rightAction : ∀ n → RightAction (M n) (≋-setoid n)
  rightAction n = record
    { _◁_        = _◁_
    ; ◁-cong     = ◁-cong
    ; ◁-identity = ◁-identity
    ; ◁-compose  = ◁-compose
    }

-- Conversely, a family of levelwise right actions on the vector
-- setoids packages as an indexed action.

indexedRightAction : {M : ℕ → RawMonoid b ℓ₂} {S : Setoid a ℓ₁} →
                     (∀ n → RightAction (M n) (VecEq.≋-setoid S n)) →
                     IndexedRightAction M S
indexedRightAction φ = record
  { _◁_        = λ {n} → RightAction._◁_        (φ n)
  ; ◁-cong     = λ {n} → RightAction.◁-cong     (φ n)
  ; ◁-identity = λ {n} → RightAction.◁-identity (φ n)
  ; ◁-compose  = λ {n} → RightAction.◁-compose  (φ n)
  }

------------------------------------------------------------------------
-- Indexed left actions

-- The same for a left action: acting by a product is acting by its
-- RIGHT factor first.  Which of the two a given semantics provides is
-- not a matter of taste — it is fixed by the order in which the
-- interpretation composes words — so both are offered.

record IndexedLeftAction (M : ℕ → RawMonoid b ℓ₂) (S : Setoid a ℓ₁) :
                         Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  private
    module M (n : ℕ) = RawMonoid (M n)
    module S = Setoid S
  open VecEq S using (_≋_)

  infixr 7 _▷_
  field
    _▷_        : ∀ {n} → M.Carrier n → Vec S.Carrier n → Vec S.Carrier n
    ▷-cong     : ∀ {n} {g g′ : M.Carrier n} {xs xs′ : Vec S.Carrier n} →
                 M._≈_ n g g′ → xs ≋ xs′ → g ▷ xs ≋ g′ ▷ xs′
    ▷-identity : ∀ {n} (xs : Vec S.Carrier n) → M.ε n ▷ xs ≋ xs
    ▷-compose  : ∀ {n} (g h : M.Carrier n) (xs : Vec S.Carrier n) →
                 (M._∙_ n g h) ▷ xs ≋ g ▷ (h ▷ xs)


------------------------------------------------------------------------
-- Consequences for indexed group actions

-- When every level of the acting family is a group, the inverse and
-- cancellation laws of Action.Group-Lemmas hold at every index.

module Group-Lemmas (G : ℕ → Group b ℓ₂) (S : Setoid a ℓ₁)
                    (φ : IndexedRightAction
                           (λ n → Group.rawMonoid (G n)) S)
                    where
  private
    module G (n : ℕ) = Group (G n)
    module S = Setoid S
  open VecEq S using (_≋_)
  open IndexedRightAction φ public using (_◁_; rightAction)

  module Levelwise (n : ℕ) =
    Action.Group-Lemmas (G n) (VecEq.≋-setoid S n) (rightAction n)

  ◁-inverseʳ : ∀ {n} (xs : Vec S.Carrier n) (g : G.Carrier n) →
               (xs ◁ g) ◁ G._⁻¹ n g ≋ xs
  ◁-inverseʳ {n} = Levelwise.◁-inverseʳ n

  ◁-inverseˡ : ∀ {n} (xs : Vec S.Carrier n) (g : G.Carrier n) →
               (xs ◁ G._⁻¹ n g) ◁ g ≋ xs
  ◁-inverseˡ {n} = Levelwise.◁-inverseˡ n

  ◁-cancelʳ : ∀ {n} (g : G.Carrier n) {xs ys : Vec S.Carrier n} →
              xs ◁ g ≋ ys ◁ g → xs ≋ ys
  ◁-cancelʳ {n} = Levelwise.◁-cancelʳ n

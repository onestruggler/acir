------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 4.3 at any internal path variable, and corollary 4.4 in any
-- elimination order
--
-- The proof of lemma 4.3 (Amy, QPL 2018) writes the phase as
-- P = y₀Q + R "for some internal path variable y₀".
-- PathSum.Clifford takes y₀ to be the first path variable.  Moving
-- y_j to the front keeps every path variable internal
-- (Reorder.Internal-front) and keeps the order of the phase
-- (Anywhere.Ord≤-front), and does not change the denotation
-- (Anywhere.Sound.front-≋).  So the head lemma, applied to
-- front j ξ, proves lemma 4.3 at every internal variable y_j
-- (lemma-4-3-at).  "Every" is stronger than the paper's "some"; the
-- paper's proof supports it, since none of its cases depends on which
-- variable is chosen.  The case the paper leaves implicit, a rule
-- that needs more normalisation than the path-sum has, is a
-- refutation here as it is at the head.
--
-- Iterating the lemma gives corollary 4.4 in any elimination order.
-- A Strategy picks, for every path-sum with a path variable left, the
-- variable to eliminate next.  Follows choose ξ ξ′ is a reduction
-- chain in which every step applies a head rule to the variable the
-- strategy picked, moved to the front.  corollary-4-4-by says that
-- under every strategy a path-sum with only internal path variables
-- and a phase of order at most 2 either reduces along that strategy
-- to one with no path variables left, or is not the identity.  The
-- strategy is part of the type, so this is more than the existence of
-- some chain.  PathSum.Anywhere.Corollary carries it to circuits.  As
-- everywhere in PathSum, the polynomial time bounds are not
-- formalised.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Anywhere.Clifford (M₀ : ℕ) where

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base
open import PathSum.Order M using (Ord≤)
open import PathSum.Reduction M using (_⟶_)
open import PathSum.Reorder using (front; Internal-front)
open import PathSum.Anywhere M using (Ord≤-front; _⟶ᵍ*_; εᵍ; _◅ᵍ_; at)
open import PathSum.Anywhere.Sound M₀ using (front-≋)

import PathSum.Denotation
module Den = PathSum.Denotation M₀

open Den using (_≋_; semantics)

import PathSum.Clifford
module Cliff = PathSum.Clifford M₀ semantics

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- Lemma 4.3 at any internal path variable

-- Lemma 4.3's progress at y_j: a head rule applies to front j ξ,
-- preserving internality and the order bound, or ξ is not the
-- identity (front j ξ is not, and it denotes what ξ does).

progress-at : (j : Fin (suc m)) (ξ : PathSum n k (suc m)) → Internal ξ →
              Ord≤ 2 (phase ξ) → Cliff.Progress (front j ξ)
progress-at j ξ int ordP =
  Cliff.progress (front j ξ) (Internal-front j ξ int) (Ord≤-front j ordP)

-- Lemma 4.3 at y_j, as the paper states it, with the step recorded as
-- a head step on front j ξ (so as the general step at j ξ ⟶ᵍ ξ′).

lemma-4-3-at : (j : Fin (suc m)) (ξ : PathSum n k (suc m)) → Internal ξ →
               Ord≤ 2 (phase ξ) → ξ ≋ idPS →
               ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ m) →
                 (front j ξ ⟶ ξ′) × Internal ξ′ × Ord≤ 2 (phase ξ′)
lemma-4-3-at {m = m} {n = n} j ξ int ordP ξ≋id =
  go (progress-at j ξ int ordP)
  where
  go : Cliff.Progress (front j ξ) →
       ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ m) →
         (front j ξ ⟶ ξ′) × Internal ξ′ × Ord≤ 2 (phase ξ′)
  go (Cliff.reduces ξ′ step int′ ord′) = _ , ξ′ , step , int′ , ord′
  go (Cliff.not-id ¬id)                = contradiction
    (Den.≋-trans {ξ = front j ξ} {ζ = ξ} {χ = idPS} (front-≋ j ξ) ξ≋id)
    ¬id


------------------------------------------------------------------------
-- Elimination orders

-- A strategy names the path variable to eliminate next.

Strategy : ℕ → Set
Strategy n = ∀ {k m} → PathSum n k (suc m) → Fin (suc m)

-- A chain that eliminates, at every step, the variable the strategy
-- picks: a head rule applied to that variable moved to the front.

infixr 5 _▸_

data Follows {n : ℕ} (choose : Strategy n) :
     ∀ {k m k′ m′} → PathSum n k m → PathSum n k′ m′ → Set where
  stop : ∀ {k m} {ξ : PathSum n k m} → Follows choose ξ ξ
  _▸_  : ∀ {k m k′ k″ m″} {ξ : PathSum n k (suc m)}
         {ζ : PathSum n k′ m} {ξ′ : PathSum n k″ m″} →
         front (choose ξ) ξ ⟶ ζ → Follows choose ζ ξ′ →
         Follows choose ξ ξ′

-- Such a chain is a chain of the general calculus.

Follows⇒⟶ᵍ* : {choose : Strategy n} {ξ : PathSum n k m}
              {ξ′ : PathSum n k′ m′} →
              Follows choose ξ ξ′ → ξ ⟶ᵍ* ξ′
Follows⇒⟶ᵍ* stop = εᵍ
Follows⇒⟶ᵍ* {choose = choose} {ξ = ξ} (s ▸ f) =
  at (choose ξ) s ◅ᵍ Follows⇒⟶ᵍ* f


------------------------------------------------------------------------
-- Corollary 4.4 along a strategy

-- Either the strategy's chain exhausts the path variables, or ξ is
-- refuted.

data ReducesBy {n : ℕ} (choose : Strategy n) {k m : ℕ}
               (ξ : PathSum n k m) : Set where
  done  : ∀ {k′} {ξ′ : PathSum n k′ 0} → Follows choose ξ ξ′ →
          ReducesBy choose ξ
  no-id : ¬ (ξ ≋ idPS) → ReducesBy choose ξ

-- The recursion of PathSum.Clifford.corollary-4-4, with lemma 4.3
-- applied at the strategy's variable instead of the first.  A
-- refutation of a reduct is carried back through the step
-- (proposition 3.1) and the renumbering.

corollary-4-4-by : (choose : Strategy n) (ξ : PathSum n k m) →
                   Internal ξ → Ord≤ 2 (phase ξ) → ReducesBy choose ξ
corollary-4-4-by {m = zero}  choose ξ int ordP = done stop
corollary-4-4-by {m = suc m} choose ξ int ordP
  with progress-at (choose ξ) ξ int ordP
... | Cliff.not-id ¬id = no-id λ ξ≋id → ¬id
  (Den.≋-trans {ξ = front (choose ξ) ξ} {ζ = ξ} {χ = idPS}
               (front-≋ (choose ξ) ξ) ξ≋id)
... | Cliff.reduces ξ′ step int′ ord′
  with corollary-4-4-by choose ξ′ int′ ord′
...   | done f    = done (step ▸ f)
...   | no-id ¬id = no-id λ ξ≋id → ¬id
  (Den.≋-trans {ξ = ξ′} {ζ = front (choose ξ) ξ} {χ = idPS}
    (Den.≋-sym {ξ = front (choose ξ) ξ} {ζ = ξ′} (Den.⟶-sound step))
    (Den.≋-trans {ξ = front (choose ξ) ξ} {ζ = ξ} {χ = idPS}
                 (front-≋ (choose ξ) ξ) ξ≋id))

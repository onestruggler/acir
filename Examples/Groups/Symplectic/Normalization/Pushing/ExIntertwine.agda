------------------------------------------------------------------------
-- Presentations of groups
--
-- The coset half of the duality intertwiner.
--
-- ExAction shows Ex acts on a doubly-inj₂ coset as the transposition of
-- the two bottom D boxes.  Write `swp` for that transposition.  The
-- intertwining law we want is
--
--   step c (dual w) ≡ swp (step (swp c) w)
--
-- and at generator level it is *definitional*: each of the five
-- generators' ract clauses commutes with swp on the nose.  That is what
-- this module records.
--
-- Note this is only the coset component.  `≋` also constrains the
-- emitted residual, and the residual half (ρ-Ex) is not established
-- here — so this is a necessary, not sufficient, ingredient for
-- DualTransport.srel-wd-dual.
--
-- SCOPE WARNING.  Everything below is stated ONLY for doubly-inj₂
-- cosets `inj₂ (d1 , inj₂ (d2 , lm))`, and it does NOT generalise:
-- `swp` is the identity on `inj₁ x` and on `inj₂ (e1 , inj₁ x)`, where
-- σ-Ex is not.  So `step c Ex ≢ swp c` off that locus, and no amount of
-- work extends these lemmas there.  Since DualTransport.srel-wd-dual
-- quantifies over ALL `c : C (₂₊ n)`, these five intertwiners cannot
-- discharge its hypotheses on their own.  Do not read `int-c10-lhs` as
-- "the coset half of c10 ⟹ c11" — it is that half on one coset shape
-- out of three (two of four at width ≥ 4).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.ExIntertwine
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime
  using (d-of-DS)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SyllableAction p-2 p-prime

module _ {m : ℕ} where

------------------------------------------------------------------------
-- The transposition of the two bottom D boxes.

  swp : C (₃₊ m) → C (₃₊ m)
  swp (inj₁ x)                    = inj₁ x
  swp (inj₂ (e1 , inj₁ x))        = inj₂ (e1 , inj₁ x)
  swp (inj₂ (e1 , inj₂ (e2 , l))) = inj₂ (e2 , inj₂ (e1 , l))

  swp-involutive : ∀ (c : C (₃₊ m)) → swp (swp c) ≡ c
  swp-involutive (inj₁ x)                    = Eq.refl
  swp-involutive (inj₂ (e1 , inj₁ x))        = Eq.refl
  swp-involutive (inj₂ (e1 , inj₂ (e2 , l))) = Eq.refl

------------------------------------------------------------------------
-- The generator-level intertwiners.
--
-- Each reads: threading the DUAL of the generator from c agrees with
-- threading the generator itself from the swapped coset, then swapping
-- back.  All five hold by refl — the ract clauses commute with swp.

  -- dual H = H ↑ : the bottom gate turns d₁; on the swapped coset the
  -- lifted gate turns the same box, now in second position.
  int-H : ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    step (₂₊ m) (inj₂ (d1 , inj₂ (d2 , lm))) (H ↑)
    ≡ swp (step (₂₊ m) (inj₂ (d2 , inj₂ (d1 , lm))) H)
  int-H d1 d2 lm = Eq.refl

  -- dual (H ↑) = H
  int-H↑ : ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    step (₂₊ m) (inj₂ (d1 , inj₂ (d2 , lm))) H
    ≡ swp (step (₂₊ m) (inj₂ (d2 , inj₂ (d1 , lm))) (H ↑))
  int-H↑ d1 d2 lm = Eq.refl

  -- dual S = S ↑
  int-S : ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    step (₂₊ m) (inj₂ (d1 , inj₂ (d2 , lm))) (S ↑)
    ≡ swp (step (₂₊ m) (inj₂ (d2 , inj₂ (d1 , lm))) S)
  int-S d1 d2 lm = Eq.refl

  -- dual (S ↑) = S
  int-S↑ : ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    step (₂₊ m) (inj₂ (d1 , inj₂ (d2 , lm))) S
    ≡ swp (step (₂₊ m) (inj₂ (d2 , inj₂ (d1 , lm))) (S ↑))
  int-S↑ d1 d2 lm = Eq.refl

  -- dual CZ = CZ : the b-shifts are symmetric under exchanging the boxes.
  int-CZ : ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    step (₂₊ m) (inj₂ (d1 , inj₂ (d2 , lm))) CZ
    ≡ swp (step (₂₊ m) (inj₂ (d2 , inj₂ (d1 , lm))) CZ)
  int-CZ d1 d2 lm = Eq.refl

------------------------------------------------------------------------
-- Consistency with ExAction: swp is exactly what Ex does.
--
-- (σ-Ex-swap states the same fact; this is the `swp` phrasing.)

  swp-is-Ex : ∀ (a1 b1 a2 b2 : ℤ ₚ) (lm : C (₁₊ m)) →
    swp (inj₂ ((a1 , b1) , inj₂ ((a2 , b2) , lm)))
    ≡ inj₂ ((a2 , b2) , inj₂ ((a1 , b1) , lm))
  swp-is-Ex a1 b1 a2 b2 lm = Eq.refl

------------------------------------------------------------------------
-- The c10/c11 left-hand sides.
--
-- c11's LHS is the dual of c10's, and both are words over the five
-- generators above.  The coset components therefore intertwine — and
-- since doubly-inj₂ is closed under these clauses, the composite is
-- again definitional.

  int-c10-lhs : ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    step (₂₊ m) (inj₂ (d1 , inj₂ (d2 , lm))) (CZ • H ↓ • CZ)
    ≡ swp (step (₂₊ m) (inj₂ (d2 , inj₂ (d1 , lm))) (CZ • H ↑ • CZ))
  int-c10-lhs d1 d2 lm = Eq.refl

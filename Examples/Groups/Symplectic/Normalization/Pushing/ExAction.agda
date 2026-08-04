------------------------------------------------------------------------
-- Presentations of groups
--
-- The coset action of Ex.
--
-- Ex = (CZ • H ↓ • H ↑) ^ 3, and on a doubly-inj₂ coset each factor acts
-- by an explicit PushML.ract clause:
--
--   CZ  : (a₁,b₁) (a₂,b₂)  ↦  (a₁, b₁ - a₂) (a₂, b₂ - a₁)
--   H ↓ : d₁ ↦ Hd' d₁                     (bottom box only)
--   H ↑ : d₂ ↦ Hd' d₂                     (recursion into the tail)
--
-- and Hd' is the quarter turn (a , b) ↦ (b , - a) (`Hd'-eq` below).
-- Composing three rounds swaps the two boxes and fixes the tail — Ex
-- acts on cosets as the wire transposition, as one would hope.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.ExAction
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Fin using (Fin)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SyllableAction p-2 p-prime

------------------------------------------------------------------------
-- Hd' is the quarter turn.
--
-- Verified pattern by pattern; note `- ₀` does not reduce to `₀`, so the
-- statement must be phrased with `- proj₁ d` rather than a normalised
-- zero.

Hd'-eq : ∀ (d : D) → Hd' d ≡ (proj₂ d , - proj₁ d)
Hd'-eq (₀ , ₀)       = Eq.refl
Hd'-eq (₀ , ₁₊ b)    = Eq.refl
Hd'-eq (₁₊ a , ₀)    = Eq.refl
Hd'-eq (₁₊ a , ₁₊ b) = Eq.refl

------------------------------------------------------------------------
-- One round of Ex.
--
-- CZ couples the two boxes by the b-shifts, then each H turns its own
-- box.  This is definitional: it is exactly the three ract clauses.

Ex-round : Circuit 2
Ex-round = CZ • H ↓ • H ↑

module _ {m : ℕ} where

  round-step : ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    step (₂₊ m) (inj₂ (d1 , inj₂ (d2 , lm))) (CZ • H ↓ • H ↑)
    ≡ inj₂ ( Hd' (proj₁ d1 , proj₂ d1 + - proj₁ d2)
           , inj₂ (Hd' (proj₁ d2 , proj₂ d2 + - proj₁ d1) , lm) )
  round-step d1 d2 lm = Eq.refl

  -- The same round with Hd' expanded by the quarter-turn law.
  round-step' : ∀ (a1 b1 a2 b2 : ℤ ₚ) (lm : C (₁₊ m)) →
    step (₂₊ m) (inj₂ ((a1 , b1) , inj₂ ((a2 , b2) , lm))) (CZ • H ↓ • H ↑)
    ≡ inj₂ ( (b1 + - a2 , - a1)
           , inj₂ ((b2 + - a1 , - a2) , lm) )
  round-step' a1 b1 a2 b2 lm =
    Eq.trans (round-step (a1 , b1) (a2 , b2) lm)
      (Eq.cong₂ (λ x y → inj₂ (x , inj₂ (y , lm)))
        (Hd'-eq (a1 , b1 + - a2))
        (Hd'-eq (a2 , b2 + - a1)))

------------------------------------------------------------------------
-- The arithmetic behind the collapse.
--
-- Every simplification in the three-round composition is this identity.

  neg-shift : ∀ (x y : ℤ ₚ) → - x + - (y + - x) ≡ - y
  neg-shift x y =
    Eq.trans (Eq.cong (- x +_) (Eq.sym (-‿+-comm y (- x))))
    (Eq.trans (Eq.cong (λ z → - x + (- y + z)) (-‿involutive x))
    (Eq.trans (Eq.sym (+-assoc (- x) (- y) x))
    (Eq.trans (Eq.cong (_+ x) (+-comm (- x) (- y)))
    (Eq.trans (+-assoc (- y) (- x) x)
    (Eq.trans (Eq.cong (- y +_) (+-inverseˡ x))
              (+-identityʳ (- y)))))))

------------------------------------------------------------------------
-- Ex is three rounds.  Both sides are the same left-to-right fold, so
-- the re-bracketing is definitional.

  Ex≡RRR : ∀ (c : C (₃₊ m)) →
    step (₂₊ m) c Ex
    ≡ step (₂₊ m) (step (₂₊ m) (step (₂₊ m) c (CZ • H ↓ • H ↑))
                                            (CZ • H ↓ • H ↑))
                                            (CZ • H ↓ • H ↑)
  Ex≡RRR c = Eq.refl

------------------------------------------------------------------------
-- Ex acts on cosets as the transposition of the two bottom D boxes.

  σ-Ex-swap : ∀ (a1 b1 a2 b2 : ℤ ₚ) (lm : C (₁₊ m)) →
    step (₂₊ m) (inj₂ ((a1 , b1) , inj₂ ((a2 , b2) , lm))) Ex
    ≡ inj₂ ((a2 , b2) , inj₂ ((a1 , b1) , lm))
  σ-Ex-swap a1 b1 a2 b2 lm =
    Eq.trans (Ex≡RRR (inj₂ ((a1 , b1) , inj₂ ((a2 , b2) , lm))))
    (Eq.trans (Eq.cong (λ x → step (₂₊ m) (step (₂₊ m) x (CZ • H ↓ • H ↑))
                                                          (CZ • H ↓ • H ↑))
                       (round-step' a1 b1 a2 b2 lm))
    (Eq.trans (Eq.cong (λ x → step (₂₊ m) x (CZ • H ↓ • H ↑))
                       (round-step' (b1 + - a2) (- a1) (b2 + - a1) (- a2) lm))
    (Eq.trans (round-step'
                 (- a1 + - (b2 + - a1)) (- (b1 + - a2))
                 (- a2 + - (b1 + - a2)) (- (b2 + - a1)) lm)
              final)))
    where
    -- After three rounds the boxes read
    --   ( -(b1-a2) + -(-a2 + -(b1-a2)) , -(-a1 + -(b2-a1)) )
    --   ( -(b2-a1) + -(-a1 + -(b2-a1)) , -(-a2 + -(b1-a2)) )
    -- and neg-shift collapses each component.
    fst₁ : - (b1 + - a2) + - (- a2 + - (b1 + - a2)) ≡ a2
    fst₁ = Eq.trans (neg-shift (b1 + - a2) (- a2)) (-‿involutive a2)

    snd₁ : - (- a1 + - (b2 + - a1)) ≡ b2
    snd₁ = Eq.trans (Eq.cong -_ (neg-shift a1 b2)) (-‿involutive b2)

    fst₂ : - (b2 + - a1) + - (- a1 + - (b2 + - a1)) ≡ a1
    fst₂ = Eq.trans (neg-shift (b2 + - a1) (- a1)) (-‿involutive a1)

    snd₂ : - (- a2 + - (b1 + - a2)) ≡ b1
    snd₂ = Eq.trans (Eq.cong -_ (neg-shift a2 b1)) (-‿involutive b1)

    final :
      inj₂ ( ( - (b1 + - a2) + - (- a2 + - (b1 + - a2))
             , - (- a1 + - (b2 + - a1)) )
           , inj₂ ( ( - (b2 + - a1) + - (- a1 + - (b2 + - a1))
                    , - (- a2 + - (b1 + - a2)) ) , lm) )
      ≡ inj₂ ((a2 , b2) , inj₂ ((a1 , b1) , lm))
    final = Eq.cong₂ (λ x y → inj₂ (x , inj₂ (y , lm)))
              (Eq.cong₂ _,_ fst₁ snd₁)
              (Eq.cong₂ _,_ fst₂ snd₂)

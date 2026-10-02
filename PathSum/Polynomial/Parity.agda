------------------------------------------------------------------------
-- Presentations of groups
--
-- The parity of an integer, as an output polynomial is read
--
-- PathSum.Polynomial.Bind's odd is the parity with which an output
-- polynomial of a path-sum is read as a Boolean polynomial
-- (PathSum.Denotation's outBit is odd of its value, by definition).
-- This module collects the arithmetic of that parity that reading
-- Boolean polynomials needs: the parity of a bit is the bit (odd-[]),
-- parity is additive (odd-+), turning a sum of 0/1 values into an
-- exclusive or, and two integers have the same parity exactly when 2
-- divides their difference (odd-≡, ≡-odd).  The facts and their
-- proofs are those of PathSum.HiddenShift.Sign, which is parameterised
-- by the precision M₀ although they are not; here they are free of it,
-- for modules that are.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial.Parity where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _xor_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; divides; ∣m+n∣m⇒∣n; ∣⇒∣ᵤ)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; *-distribʳ-+)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Product.Base using (Σ; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Order 0 using (parity)
open import PathSum.Polynomial.Bind using (odd)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)


------------------------------------------------------------------------
-- Even and odd

private
  2∤1 : ¬ ((+ 2) ∣ 1ℤ)
  2∤1 h with ∣1⇒≡1 (∣⇒∣ᵤ h)
  ... | ()

odd-even : ∀ {z} → (+ 2) ∣ z → odd z ≡ false
odd-even {z} d with (+ 2) ∣? z
... | yes _  = refl
... | no ¬d = contradiction d ¬d

odd-odd : ∀ {z} → ¬ ((+ 2) ∣ z) → odd z ≡ true
odd-odd {z} ¬d with (+ 2) ∣? z
... | yes d = contradiction d ¬d
... | no _  = refl

-- An odd number is not 0.

odd-0 : odd 0ℤ ≡ false
odd-0 = odd-even (divides 0ℤ refl)

odd⇒≢0 : ∀ {z} → odd z ≡ true → z ≢ 0ℤ
odd⇒≢0 {z} h refl with trans (sym h) odd-0
... | ()


------------------------------------------------------------------------
-- Bits

-- The parity of r·2 + b is b.

odd-rep : ∀ r b → odd (r * (+ 2) + [ b ]ᶻ) ≡ b
odd-rep r false = odd-even (divides r (+-identityʳ (r * (+ 2))))
odd-rep r true  = odd-odd (λ d → 2∤1 (∣m+n∣m⇒∣n d (divides r refl)))

odd-[] : ∀ b → odd [ b ]ᶻ ≡ b
odd-[] b = trans (cong odd (sym (+-identityˡ [ b ]ᶻ))) (odd-rep 0ℤ b)

-- Every integer is twice something plus its parity.

halve : ∀ a → Σ ℤ (λ r → a ≡ r * (+ 2) + [ odd a ]ᶻ)
halve a with parity a
... | inj₁ (r , eq) = r , trans eq (sym (trans
        (cong (λ b → r * (+ 2) + [ b ]ᶻ) (odd-even (divides r eq)))
        (+-identityʳ (r * (+ 2)))))
... | inj₂ (r , eq) = r , trans eq
        (cong (λ b → r * (+ 2) + [ b ]ᶻ)
              (sym (odd-odd (λ d → 2∤1 (∣m+n∣m⇒∣n (subst ((+ 2) ∣_) eq d)
                                                   (divides r refl))))))


------------------------------------------------------------------------
-- Parity is additive

odd-+ : ∀ a b → odd (a + b) ≡ odd a xor odd b
odd-+ a b with halve a | halve b
... | ra , ea | rb , eb =
  trans (cong odd whole) (odd-rep (ra + rb + [ p ∧ q ]ᶻ) (p xor q))
  where
  p q : Bool
  p = odd a
  q = odd b

  carry : ∀ s t → [ s ]ᶻ + [ t ]ᶻ ≡ [ s ∧ t ]ᶻ * (+ 2) + [ s xor t ]ᶻ
  carry false false = refl
  carry false true  = refl
  carry true  false = refl
  carry true  true  = refl

  regroup : ∀ u v s t →
            (u * (+ 2) + s) + (v * (+ 2) + t) ≡ ((u + v) * (+ 2)) + (s + t)
  regroup = solve 4 (λ u v s t →
    (u :* con (+ 2) :+ s) :+ (v :* con (+ 2) :+ t) :=
    ((u :+ v) :* con (+ 2)) :+ (s :+ t)) refl

  whole : a + b ≡ (ra + rb + [ p ∧ q ]ᶻ) * (+ 2) + [ p xor q ]ᶻ
  whole = trans (cong₂ _+_ ea eb)
    (trans (regroup ra rb [ p ]ᶻ [ q ]ᶻ)
      (trans (cong (λ t → (ra + rb) * (+ 2) + t) (carry p q))
        (sym (trans (cong (_+ [ p xor q ]ᶻ)
                          (*-distribʳ-+ (+ 2) (ra + rb) [ p ∧ q ]ᶻ))
                    (solve 3 (λ u w t → (u :+ w) :+ t := u :+ (w :+ t)) refl
                             ((ra + rb) * (+ 2)) ([ p ∧ q ]ᶻ * (+ 2))
                             [ p xor q ]ᶻ)))))


------------------------------------------------------------------------
-- Same parity, even difference

odd-≡ : ∀ a b → odd a ≡ odd b → (+ 2) ∣ (a - b)
odd-≡ a b eq with halve a | halve b
... | ra , ea | rb , eb = divides (ra - rb) (trans
  (cong₂ _-_ ea (trans eb (cong (λ t → rb * (+ 2) + [ t ]ᶻ) (sym eq))))
  (shape ra rb [ odd a ]ᶻ))
  where
  shape : ∀ u v t → (u * (+ 2) + t) - (v * (+ 2) + t) ≡ (u - v) * (+ 2)
  shape = solve 3 (λ u v t → (u :* con (+ 2) :+ t) :- (v :* con (+ 2) :+ t)
                             := (u :- v) :* con (+ 2)) refl

≡-odd : ∀ a b → (+ 2) ∣ (a - b) → odd a ≡ odd b
≡-odd a b d = trans (cong odd (split a b))
  (trans (odd-+ (a - b) b) (cong (_xor odd b) (odd-even d)))
  where
  split : ∀ a b → a ≡ (a - b) + b
  split = solve 2 (λ a b → a := (a :- b) :+ b) refl

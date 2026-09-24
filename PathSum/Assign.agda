------------------------------------------------------------------------
-- Presentations of groups
--
-- Boolean assignments: updating one bit, and comparing two
--
-- Lemma 4.1 and the circuit semantics both look at an assignment with
-- one wire overwritten, and both ask whether two assignments agree.
-- The definitions are gathered here so that every module that splits
-- a sum at a wire, or tests for the diagonal, uses the same ones.
-- Assignments are plain functions Fin k → Bool, so equal ones are
-- only pointwise equal, and every lemma here is stated pointwise.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Assign where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _xor_;
  if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Fin.Properties as Fin

private
  variable
    k : ℕ


------------------------------------------------------------------------
-- A bit as an integer

[_]ᶻ : Bool → ℤ
[ b ]ᶻ = if b then 1ℤ else 0ℤ


------------------------------------------------------------------------
-- Overwriting one bit

infixl 9 _[_≔_]

_[_≔_] : (Fin k → Bool) → Fin k → Bool → (Fin k → Bool)
(z [ i ≔ b ]) j = if ⌊ j Fin.≟ i ⌋ then b else z j

≔-here : (z : Fin k → Bool) (i : Fin k) (b : Bool) → (z [ i ≔ b ]) i ≡ b
≔-here z i b with i Fin.≟ i
... | yes _ = refl
... | no ¬p = contradiction refl ¬p

≔-there : (z : Fin k → Bool) {i j : Fin k} (b : Bool) → j ≢ i →
          (z [ i ≔ b ]) j ≡ z j
≔-there z {i} {j} b j≢i with j Fin.≟ i
... | yes p = contradiction p j≢i
... | no  _ = refl

-- Writing a bit back leaves the assignment as it was.

≔-self : (z : Fin k → Bool) (i : Fin k) → ∀ j → (z [ i ≔ z i ]) j ≡ z j
≔-self z i j with j Fin.≟ i
... | yes refl = refl
... | no  _    = refl

-- A second write to the same bit overrides the first.

≔-≔ : (z : Fin k → Bool) (i : Fin k) (b b′ : Bool) →
      ∀ j → ((z [ i ≔ b ]) [ i ≔ b′ ]) j ≡ (z [ i ≔ b′ ]) j
≔-≔ z i b b′ j with j Fin.≟ i
... | yes _ = refl
... | no  _ = refl

-- Writes to two different bits commute.

≔-comm : (z : Fin k → Bool) {i i′ : Fin k} (b b′ : Bool) → i ≢ i′ →
         ∀ j → ((z [ i ≔ b ]) [ i′ ≔ b′ ]) j ≡ ((z [ i′ ≔ b′ ]) [ i ≔ b ]) j
≔-comm z {i} {i′} b b′ i≢i′ j with j Fin.≟ i | j Fin.≟ i′
... | yes refl | yes refl = contradiction refl i≢i′
... | yes refl | no  _    = refl
... | no  _    | yes _    = refl
... | no  _    | no  _    = refl

-- Updating pointwise-equal assignments gives pointwise-equal results.

≔-cong : {z z′ : Fin k → Bool} (i : Fin k) (b : Bool) →
         (∀ j → z j ≡ z′ j) → ∀ j → (z [ i ≔ b ]) j ≡ (z′ [ i ≔ b ]) j
≔-cong {z = z} {z′} i b z≗z′ j with j Fin.≟ i
... | yes _ = refl
... | no  _ = z≗z′ j


------------------------------------------------------------------------
-- Comparing bits and assignments

infix 4 _=ᵇ_

_=ᵇ_ : Bool → Bool → Bool
a =ᵇ b = not (a xor b)

=ᵇ-refl : ∀ b → (b =ᵇ b) ≡ true
=ᵇ-refl true  = refl
=ᵇ-refl false = refl

=ᵇ-true : ∀ {a b} → (a =ᵇ b) ≡ true → a ≡ b
=ᵇ-true {true}  {true}  _ = refl
=ᵇ-true {false} {false} _ = refl
=ᵇ-true {true}  {false} ()
=ᵇ-true {false} {true}  ()

=ᵇ-false : ∀ {a b} → (a =ᵇ b) ≡ false → a ≢ b
=ᵇ-false {true}  {true}  () _
=ᵇ-false {false} {false} () _
=ᵇ-false {true}  {false} _ ()
=ᵇ-false {false} {true}  _ ()

-- Whether two assignments agree on every bit.

same : (Fin k → Bool) → (Fin k → Bool) → Bool
same {ℕ.zero}  x z = true
same {ℕ.suc k} x z = (x zero =ᵇ z zero) ∧ same (λ j → x (suc j)) (λ j → z (suc j))

same-refl : (x : Fin k → Bool) → same x x ≡ true
same-refl {ℕ.zero}  x = refl
same-refl {ℕ.suc k} x rewrite =ᵇ-refl (x zero) = same-refl (λ j → x (suc j))

same-true : (x z : Fin k → Bool) → same x z ≡ true → ∀ j → x j ≡ z j
same-true {ℕ.suc k} x z h j with x zero =ᵇ z zero in eq
same-true {ℕ.suc k} x z h zero    | true = =ᵇ-true eq
same-true {ℕ.suc k} x z h (suc j) | true =
  same-true (λ i → x (suc i)) (λ i → z (suc i)) h j
same-true {ℕ.suc k} x z () j      | false

same-intro : (x z : Fin k → Bool) → (∀ j → x j ≡ z j) → same x z ≡ true
same-intro {ℕ.zero}  x z h = refl
same-intro {ℕ.suc k} x z h
  rewrite h zero | =ᵇ-refl (z zero) =
  same-intro (λ j → x (suc j)) (λ j → z (suc j)) (λ j → h (suc j))

same-false : (x z : Fin k → Bool) → same x z ≡ false →
             ¬ (∀ j → x j ≡ z j)
same-false x z h x≗z with trans (sym h) (same-intro x z x≗z)
... | ()

-- Only the values are compared.

same-≗ : {x x′ z z′ : Fin k → Bool} → (∀ j → x j ≡ x′ j) →
         (∀ j → z j ≡ z′ j) → same x z ≡ same x′ z′
same-≗ {ℕ.zero}  x≗x′ z≗z′ = refl
same-≗ {ℕ.suc k} x≗x′ z≗z′ rewrite x≗x′ zero | z≗z′ zero =
  cong (_ ∧_) (same-≗ (λ j → x≗x′ (suc j)) (λ j → z≗z′ (suc j)))

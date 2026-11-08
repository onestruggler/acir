------------------------------------------------------------------------
-- Presentations of groups
--
-- Equality of computed matrices decided by one boolean.
--
-- `refl` between two computed matrices makes Agda compare them entry by
-- entry, and each entry is reduced afresh from the unevaluated product:
-- what one reduction shares is lost before the next.  eqM computes the
-- whole comparison in one reduction, and eqM-sound turns its `true`
-- into the equation.  Give eqM-sound both matrices: eqM is a function,
-- so they cannot be read back off its type.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Decide where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Decidable.Core using (does ; yes ; no)
open import Quantum.Synthesis.Matrix using (Matrix ; Matrix')

private
  ∧-true : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-true {true}  {true}  Eq.refl = Eq.refl , Eq.refl
  ∧-true {true}  {false} ()
  ∧-true {false} ()

module Over {A : Set} (_≟_ : DecidableEquality A) where

  eqA : A → A → Bool
  eqA x y = does (x ≟ y)

  eqA-sound : ∀ x y → eqA x y ≡ true → x ≡ y
  eqA-sound x y h with x ≟ y
  eqA-sound x y h  | yes p = p
  eqA-sound x y () | no _

  eqV : ∀ {n} → Vec A n → Vec A n → Bool
  eqV []       []       = true
  eqV (x ∷ xs) (y ∷ ys) = eqA x y ∧ eqV xs ys

  eqV-sound : ∀ {n} (xs ys : Vec A n) → eqV xs ys ≡ true → xs ≡ ys
  eqV-sound []       []       _ = Eq.refl
  eqV-sound (x ∷ xs) (y ∷ ys) h with ∧-true {eqA x y} h
  ... | h₁ , h₂ = Eq.cong₂ _∷_ (eqA-sound x y h₁) (eqV-sound xs ys h₂)

  eqVV : ∀ {m n} → Vec (Vec A m) n → Vec (Vec A m) n → Bool
  eqVV []       []       = true
  eqVV (x ∷ xs) (y ∷ ys) = eqV x y ∧ eqVV xs ys

  eqVV-sound : ∀ {m n} (xs ys : Vec (Vec A m) n) → eqVV xs ys ≡ true → xs ≡ ys
  eqVV-sound []       []       _ = Eq.refl
  eqVV-sound (x ∷ xs) (y ∷ ys) h with ∧-true {eqV x y} h
  ... | h₁ , h₂ = Eq.cong₂ _∷_ (eqV-sound x y h₁) (eqVV-sound xs ys h₂)

  eqM : ∀ {m n} → Matrix m n A → Matrix m n A → Bool
  eqM (Matrix' a) (Matrix' b) = eqVV a b

  eqM-sound : ∀ {m n} (M N : Matrix m n A) → eqM M N ≡ true → M ≡ N
  eqM-sound (Matrix' a) (Matrix' b) h = Eq.cong Matrix' (eqVV-sound a b h)

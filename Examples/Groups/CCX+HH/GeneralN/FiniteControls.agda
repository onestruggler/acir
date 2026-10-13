------------------------------------------------------------------------
-- Presentations of groups
--
-- Finite families of controls: their Boolean conjunction, distinctness
-- and freshness, without assumptions about the control values.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Examples.Groups.CCX+HH.GeneralN.FiniteControls
  (Wire : Set) (_≟_ : DecidableEquality Wire) where

open import Data.Bool.Base using (Bool ; false ; true ; _∧_)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; cong₂)
import Examples.Groups.CCX+HH.GeneralN.ControlledX as Controlled
open Controlled Wire _≟_ using (Fresh ; Distinct ; controls)

all : ∀ n → (Fin n → Bool) → Bool
all zero p = true
all (suc n) p = p zero ∧ all n (λ i → p (suc i))

all-cong : ∀ n {p q} → (∀ i → p i ≡ q i) → all n p ≡ all n q
all-cong zero eq = refl
all-cong (suc n) eq = cong₂ _∧_ (eq zero) (all-cong n (λ i → eq (suc i)))

all-ones : ∀ n → all n (λ _ → true) ≡ true
all-ones zero = refl
all-ones (suc n) = all-ones n

private
  ∧-trueˡ : ∀ a b → a ∧ b ≡ true → a ≡ true
  ∧-trueˡ false b ()
  ∧-trueˡ true b eq = refl
  ∧-trueʳ : ∀ a b → a ∧ b ≡ true → b ≡ true
  ∧-trueʳ false b ()
  ∧-trueʳ true b eq = eq

all-true : ∀ n p → all n p ≡ true → ∀ i → p i ≡ true
all-true zero p eq ()
all-true (suc n) p eq zero = ∧-trueˡ (p zero) (all n (λ i → p (suc i))) eq
all-true (suc n) p eq (suc i) = all-true n (λ j → p (suc j))
  (∧-trueʳ (p zero) (all n (λ j → p (suc j))) eq) i

fresh-tabulate : ∀ n (f : Fin n → Wire) a → (∀ i → a ≢ f i) → Fresh a (tabulate f)
fresh-tabulate zero f a ne = tt
fresh-tabulate (suc n) f a ne = ne zero , fresh-tabulate n (λ i → f (suc i)) a (λ i → ne (suc i))

distinct-tabulate : ∀ n (f : Fin n → Wire) →
  (∀ {i j} → f i ≡ f j → i ≡ j) → Distinct (tabulate f)
distinct-tabulate zero f inj = tt
distinct-tabulate (suc n) f inj =
  fresh-tabulate n (λ i → f (suc i)) (f zero) (λ i eq → impossible (inj eq)) ,
  distinct-tabulate n (λ i → f (suc i)) (λ eq → successor (inj eq))
  where
  impossible : ∀ {i : Fin n} → zero ≢ suc i
  impossible ()
  successor : ∀ {i j : Fin n} → suc i ≡ suc j → i ≡ j
  successor refl = refl

controls-tabulate : ∀ n (f : Fin n → Wire) s → controls (tabulate f) s ≡ all n (λ i → s (f i))
controls-tabulate zero f s = refl
controls-tabulate (suc n) f s = cong₂ _∧_ refl (controls-tabulate n (λ i → f (suc i)) s)

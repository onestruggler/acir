------------------------------------------------------------------------
-- Presentations of groups
--
-- Facts about functions on the eight basis states, decided by
-- evaluation: two functions agree on the states below j (agree), and a
-- concrete list of states is duplicate-free (distinct).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Check where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; if_then_else_ ; T ; not)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ ; _<ᵇ_ ; _<_)
open import Data.Nat.Properties using (<⇒<ᵇ)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable using (does)

open import Examples.Groups.Symmetric.CoxeterFrames using (Avoid ; Distinct ; [] ; _∷_)

eqᵇ : Fin 8 → Fin 8 → Bool
eqᵇ x y = does (x FinP.≟ y)

eqᵇ-sound : (x y : Fin 8) → eqᵇ x y ≡ true → x ≡ y
eqᵇ-sound x y h with x FinP.≟ y
eqᵇ-sound x y h  | yes e = e
eqᵇ-sound x y () | no _

private
  ∧-l : ∀ {p q} → p ∧ q ≡ true → p ≡ true
  ∧-l {true} _ = Eq.refl
  ∧-r : ∀ {p q} → p ∧ q ≡ true → q ≡ true
  ∧-r {true} h = h

fins8 : List (Fin 8)
fins8 = zero ∷ suc zero ∷ suc (suc zero) ∷ suc (suc (suc zero)) ∷ suc (suc (suc (suc zero)))
  ∷ suc (suc (suc (suc (suc zero)))) ∷ suc (suc (suc (suc (suc (suc zero)))))
  ∷ suc (suc (suc (suc (suc (suc (suc zero)))))) ∷ []

data In (x : Fin 8) : List (Fin 8) → Set where
  here  : ∀ {xs} → In x (x ∷ xs)
  there : ∀ {y xs} → In x xs → In x (y ∷ xs)

in8 : (x : Fin 8) → In x fins8
in8 zero = here
in8 (suc zero) = there here
in8 (suc (suc zero)) = there (there here)
in8 (suc (suc (suc zero))) = there (there (there here))
in8 (suc (suc (suc (suc zero)))) = there (there (there (there here)))
in8 (suc (suc (suc (suc (suc zero))))) = there (there (there (there (there here))))
in8 (suc (suc (suc (suc (suc (suc zero)))))) = there (there (there (there (there (there here)))))
in8 (suc (suc (suc (suc (suc (suc (suc zero))))))) = there (there (there (there (there (there (there here))))))

allL : (Fin 8 → Bool) → List (Fin 8) → Bool
allL P []       = true
allL P (x ∷ xs) = P x ∧ allL P xs

allL-sound : (P : Fin 8 → Bool) (xs : List (Fin 8)) → allL P xs ≡ true → ∀ {x} → In x xs → P x ≡ true
allL-sound P (y ∷ ys) h here      = ∧-l {P y} {allL P ys} h
allL-sound P (y ∷ ys) h (there i) = allL-sound P ys (∧-r {P y} {allL P ys} h) i

all8 : (Fin 8 → Bool) → Bool
all8 P = allL P fins8

all8-sound : (P : Fin 8 → Bool) → all8 P ≡ true → ∀ x → P x ≡ true
all8-sound P h x = allL-sound P fins8 h (in8 x)

-- f and g agree on the states below j.
below : ℕ → (Fin 8 → Fin 8) → (Fin 8 → Fin 8) → Fin 8 → Bool
below j f g x = if toℕ x <ᵇ j then eqᵇ (f x) (g x) else true

agree : (j : ℕ) (f g : Fin 8 → Fin 8) → all8 (below j f g) ≡ true → ∀ x → toℕ x < j → f x ≡ g x
agree j f g h x lt = eqᵇ-sound (f x) (g x) (use (toℕ x <ᵇ j) (lift (<⇒<ᵇ lt)) (all8-sound (below j f g) h x))
  where
  lift : ∀ {b} → T b → b ≡ true
  lift {true} _ = Eq.refl
  use : ∀ b {t} → b ≡ true → (if b then t else true) ≡ true → t ≡ true
  use true Eq.refl h = h

everywhere : (f g : Fin 8 → Fin 8) → all8 (λ x → eqᵇ (f x) (g x)) ≡ true → ∀ x → f x ≡ g x
everywhere f g h x = eqᵇ-sound (f x) (g x) (all8-sound (λ y → eqᵇ (f y) (g y)) h x)

------------------------------------------------------------------------
-- Duplicate-free lists of states, decided

notIn : Fin 8 → List (Fin 8) → Bool
notIn x []       = true
notIn x (y ∷ ys) = not (eqᵇ x y) ∧ notIn x ys

distinctᵇ : List (Fin 8) → Bool
distinctᵇ []       = true
distinctᵇ (x ∷ xs) = notIn x xs ∧ distinctᵇ xs

private
  ne : (x y : Fin 8) → not (eqᵇ x y) ≡ true → x ≢ y
  ne x y h e with x FinP.≟ y
  ne x y () e | yes _
  ne x y h  e | no n = n e

  avoid : (x : Fin 8) (ys : List (Fin 8)) → notIn x ys ≡ true → Avoid x ys
  avoid x []       h = []
  avoid x (y ∷ ys) h = ne x y (∧-l {not (eqᵇ x y)} {notIn x ys} h) ∷ avoid x ys (∧-r {not (eqᵇ x y)} {notIn x ys} h)

distinct : (xs : List (Fin 8)) → distinctᵇ xs ≡ true → Distinct xs
distinct []       h = []
distinct (x ∷ xs) h = avoid x xs (∧-l {notIn x xs} {distinctᵇ xs} h) ∷ distinct xs (∧-r {notIn x xs} {distinctᵇ xs} h)

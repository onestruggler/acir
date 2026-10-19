------------------------------------------------------------------------
-- Presentations of groups
--
-- The eight levels of three wires: XOR, equality, and finite checks.
--
-- `allFin n p` checks p at every element of Fin n; `allFin-sound`
-- turns a successful check into the statement for all of them, so that
-- facts about levels are decided by one boolean.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8 where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; T)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst ; sym)
open import Data.Unit.Base using (tt)
open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

------------------------------------------------------------------------
-- Checks over a finite type

private
  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} _ = refl

  ∧-r : ∀ a {b} → a ∧ b ≡ true → b ≡ true
  ∧-r true h = h

allFin : ∀ n → (Fin n → Bool) → Bool
allFin zero    p = true
allFin (suc n) p = p zero ∧ allFin n (λ i → p (suc i))

allFin-sound : ∀ n (p : Fin n → Bool) → allFin n p ≡ true → ∀ i → p i ≡ true
allFin-sound (suc n) p h zero    = ∧-l h
allFin-sound (suc n) p h (suc i) = allFin-sound n (λ j → p (suc j)) (∧-r (p zero) h) i

------------------------------------------------------------------------
-- Equality of levels

eqF : ∀ {n} → Fin n → Fin n → Bool
eqF a b = toℕ a ≡ᵇ toℕ b

eqF-sound : ∀ {n} (a b : Fin n) → eqF a b ≡ true → a ≡ b
eqF-sound a b h = toℕ-injective (≡ᵇ⇒≡ (toℕ a) (toℕ b) (subst T (sym h) tt))

------------------------------------------------------------------------
-- XOR of levels

infixl 6 _⊕_
_⊕_ : Fin 8 → Fin 8 → Fin 8
₀ ⊕ ₀ = ₀
₀ ⊕ ₁ = ₁
₀ ⊕ ₂ = ₂
₀ ⊕ ₃ = ₃
₀ ⊕ ₄ = ₄
₀ ⊕ ₅ = ₅
₀ ⊕ ₆ = ₆
₀ ⊕ ₇ = ₇
₁ ⊕ ₀ = ₁
₁ ⊕ ₁ = ₀
₁ ⊕ ₂ = ₃
₁ ⊕ ₃ = ₂
₁ ⊕ ₄ = ₅
₁ ⊕ ₅ = ₄
₁ ⊕ ₆ = ₇
₁ ⊕ ₇ = ₆
₂ ⊕ ₀ = ₂
₂ ⊕ ₁ = ₃
₂ ⊕ ₂ = ₀
₂ ⊕ ₃ = ₁
₂ ⊕ ₄ = ₆
₂ ⊕ ₅ = ₇
₂ ⊕ ₆ = ₄
₂ ⊕ ₇ = ₅
₃ ⊕ ₀ = ₃
₃ ⊕ ₁ = ₂
₃ ⊕ ₂ = ₁
₃ ⊕ ₃ = ₀
₃ ⊕ ₄ = ₇
₃ ⊕ ₅ = ₆
₃ ⊕ ₆ = ₅
₃ ⊕ ₇ = ₄
₄ ⊕ ₀ = ₄
₄ ⊕ ₁ = ₅
₄ ⊕ ₂ = ₆
₄ ⊕ ₃ = ₇
₄ ⊕ ₄ = ₀
₄ ⊕ ₅ = ₁
₄ ⊕ ₆ = ₂
₄ ⊕ ₇ = ₃
₅ ⊕ ₀ = ₅
₅ ⊕ ₁ = ₄
₅ ⊕ ₂ = ₇
₅ ⊕ ₃ = ₆
₅ ⊕ ₄ = ₁
₅ ⊕ ₅ = ₀
₅ ⊕ ₆ = ₃
₅ ⊕ ₇ = ₂
₆ ⊕ ₀ = ₆
₆ ⊕ ₁ = ₇
₆ ⊕ ₂ = ₄
₆ ⊕ ₃ = ₅
₆ ⊕ ₄ = ₂
₆ ⊕ ₅ = ₃
₆ ⊕ ₆ = ₀
₆ ⊕ ₇ = ₁
₇ ⊕ ₀ = ₇
₇ ⊕ ₁ = ₆
₇ ⊕ ₂ = ₅
₇ ⊕ ₃ = ₄
₇ ⊕ ₄ = ₃
₇ ⊕ ₅ = ₂
₇ ⊕ ₆ = ₁
₇ ⊕ ₇ = ₀

-- (a ⊕ c) ⊕ (b ⊕ c) is a ⊕ b.
xor-cancel : ∀ a b c → (a ⊕ c) ⊕ (b ⊕ c) ≡ a ⊕ b
xor-cancel a b c = eqF-sound _ _
  (allFin-sound 8 (test a b) (allFin-sound 8 (λ b → allFin 8 (test a b))
    (allFin-sound 8 (λ a → allFin 8 (λ b → allFin 8 (test a b))) refl a) b) c)
  where
  test : Fin 8 → Fin 8 → Fin 8 → Bool
  test a b c = eqF ((a ⊕ c) ⊕ (b ⊕ c)) (a ⊕ b)

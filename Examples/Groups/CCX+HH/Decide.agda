------------------------------------------------------------------------
-- Presentations of groups
--
-- Boolean equality of EucDomain matrices over 𝔻 = ℤ[1/2] and over
-- 𝔻[√2] = ℤ[1/√2], for proving matrix identities by evaluation.
--
-- A matrix identity proved by `refl` makes the conversion checker
-- compare the two sides entry by entry, and what one entry computed is
-- lost to the next.  `by-eq tt` (`by-eq√ tt` over 𝔻[√2], `by-eqᵛ tt`
-- for vectors) reduces one boolean instead, which Agda's reduction
-- machine evaluates with sharing.  A single dyadic is cheap to compare
-- by `refl`; a scalar version of `by-eq`, used in a definition of 135
-- clauses (`ThreeQubit/Signature`), exhausted a 4.5 GB heap.  Both rings store their elements canonically (a dyadic is
-- a / 2ⁿ with a odd or n = 0, the proof of which is irrelevant), so
-- equality is equality of the integers and exponents.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Decide where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; T)
open import Data.Integer.Base using (ℤ ; +_ ; -[1+_])
open import Data.Nat.Base using (ℕ ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡ ; ≡⇒≡ᵇ)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)

open import Quantum.Synthesis.Ring using (Dyadic ; Dyadic' ; _[√2] ; RootTwo)
open import Quantum.Synthesis.Matrix using (Matrix ; Matrix')

private
  variable
    m n : ℕ
    A : Set

  T-∧ : ∀ {x y} → T (x ∧ y) → T x × T y
  T-∧ {true} {true} _ = tt , tt

------------------------------------------------------------------------
-- Integers, dyadic rationals and 𝔻[√2]

eqℤ : ℤ → ℤ → Bool
eqℤ (+ m) (+ n) = m ≡ᵇ n
eqℤ -[1+ m ] -[1+ n ] = m ≡ᵇ n
eqℤ _ _ = false

eqℤ-sound : ∀ a b → T (eqℤ a b) → a ≡ b
eqℤ-sound (+ m) (+ n) p = cong +_ (≡ᵇ⇒≡ m n p)
eqℤ-sound -[1+ m ] -[1+ n ] p = cong -[1+_] (≡ᵇ⇒≡ m n p)

eqD : Dyadic → Dyadic → Bool
eqD (Dyadic' a m _) (Dyadic' b n _) = eqℤ a b ∧ (m ≡ᵇ n)

eqD-sound : ∀ x y → T (eqD x y) → x ≡ y
eqD-sound (Dyadic' a m _) (Dyadic' b n _) p with T-∧ {eqℤ a b} p
... | pa , pm with eqℤ-sound a b pa | ≡ᵇ⇒≡ m n pm
... | refl | refl = refl

eqD√ : Dyadic [√2] → Dyadic [√2] → Bool
eqD√ (RootTwo a b) (RootTwo c d) = eqD a c ∧ eqD b d

eqD√-sound : ∀ x y → T (eqD√ x y) → x ≡ y
eqD√-sound (RootTwo a b) (RootTwo c d) p with T-∧ {eqD a c} p
... | pa , pb = cong₂ RootTwo (eqD-sound a c pa) (eqD-sound b d pb)

------------------------------------------------------------------------
-- Vectors and matrices

eqVec : (A → A → Bool) → Vec A n → Vec A n → Bool
eqVec eq [] [] = true
eqVec eq (x ∷ xs) (y ∷ ys) = eq x y ∧ eqVec eq xs ys

eqVec-sound : (eq : A → A → Bool) → (∀ x y → T (eq x y) → x ≡ y) →
  (xs ys : Vec A n) → T (eqVec eq xs ys) → xs ≡ ys
eqVec-sound eq ok [] [] _ = refl
eqVec-sound eq ok (x ∷ xs) (y ∷ ys) p with T-∧ {eq x y} p
... | px , pxs = cong₂ _∷_ (ok x y px) (eqVec-sound eq ok xs ys pxs)

eqMat : (A → A → Bool) → Matrix m n A → Matrix m n A → Bool
eqMat eq (Matrix' a) (Matrix' b) = eqVec (eqVec eq) a b

eqMat-sound : (eq : A → A → Bool) → (∀ x y → T (eq x y) → x ≡ y) →
  (M N : Matrix m n A) → T (eqMat eq M N) → M ≡ N
eqMat-sound eq ok (Matrix' a) (Matrix' b) p =
  cong Matrix' (eqVec-sound (eqVec eq) (eqVec-sound eq ok) a b p)

------------------------------------------------------------------------
-- Reflexivity

private
  T-∧-intro : ∀ {x y} → T x → T y → T (x ∧ y)
  T-∧-intro {true} _ q = q

eqℤ-refl : ∀ a → T (eqℤ a a)
eqℤ-refl (+ m) = ≡⇒≡ᵇ m m refl
eqℤ-refl -[1+ m ] = ≡⇒≡ᵇ m m refl

eqD-refl : ∀ x → T (eqD x x)
eqD-refl (Dyadic' a m _) = T-∧-intro (eqℤ-refl a) (≡⇒≡ᵇ m m refl)

eqVec-refl : (eq : A → A → Bool) → (∀ x → T (eq x x)) → (xs : Vec A n) → T (eqVec eq xs xs)
eqVec-refl eq r [] = tt
eqVec-refl eq r (x ∷ xs) = T-∧-intro (r x) (eqVec-refl eq r xs)

eqMat-refl : (eq : A → A → Bool) → (∀ x → T (eq x x)) → (M : Matrix m n A) → T (eqMat eq M M)
eqMat-refl eq r (Matrix' a) = eqVec-refl (eqVec eq) (eqVec-refl eq r) a

------------------------------------------------------------------------
-- Identities by evaluation

by-eqᵛ : {u v : Vec Dyadic n} → T (eqVec eqD u v) → u ≡ v
by-eqᵛ {u = u} {v} = eqVec-sound eqD eqD-sound u v

by-eq : {M N : Matrix m n Dyadic} → T (eqMat eqD M N) → M ≡ N
by-eq {M = M} {N} = eqMat-sound eqD eqD-sound M N

by-eq√ : {M N : Matrix m n (Dyadic [√2])} → T (eqMat eqD√ M N) → M ≡ N
by-eq√ {M = M} {N} = eqMat-sound eqD√ eqD√-sound M N

------------------------------------------------------------------------
-- Presentations of groups
--
-- The rings ℤ[x]/(x⁴ − p x² − q)
--
-- The matrices of the gates, with their factors 1/√d taken out, have
-- entries in ℤ[ω] (ω = e^{iπ/4}, ω⁴ = −1) for qubits and in ℤ[ζ]
-- (ζ = e^{iπ/6}, ζ⁴ = ζ² − 1) for qutrits.  Both are ℤ⁴ with the
-- multiplication of ℤ[x]/(x⁴ − p x² − q), at (p , q) = (0 , −1) and
-- (1 , −1).  Elements are plain quadruples of integers, so that the
-- relations are checked by evaluation, with a decidable equality.
--
-- The multiplication is written once over any carrier (Mul), so that
-- the integer ring solver can be handed the very terms it computes:
-- each ring law is four polynomial identities in the coefficients and
-- in p and q.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Integer.Base using (ℤ)

module Examples.Independence.Semantics.Quartic (p q : ℤ) where

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Integer.Base as ℤ using (+_ ; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Relation.Nullary using (yes ; no)

open +-*-Solver using (solve ; _:=_ ; _:+_ ; _:*_ ; con)

------------------------------------------------------------------------
-- The multiplication over any carrier

-- Quadruples (c₀ , c₁ , c₂ , c₃), for c₀ + c₁ x + c₂ x² + c₃ x³.
Q⁴ : Set → Set
Q⁴ A = A × A × A × A

module Mul {A : Set} (_⊕_ _⊗_ : A → A → A) (p q : A) where

  -- x⁴ = p x² + q, x⁵ = p x³ + q x and x⁶ = (p² + q) x² + p q.
  mul : Q⁴ A → Q⁴ A → Q⁴ A
  mul (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃) =
      (s₀ ⊕ (q ⊗ s₄)) ⊕ ((p ⊗ q) ⊗ s₆)
    , s₁ ⊕ (q ⊗ s₅)
    , (s₂ ⊕ (p ⊗ s₄)) ⊕ (((p ⊗ p) ⊕ q) ⊗ s₆)
    , s₃ ⊕ (p ⊗ s₅)
    where
    s₀ = a₀ ⊗ b₀
    s₁ = (a₀ ⊗ b₁) ⊕ (a₁ ⊗ b₀)
    s₂ = ((a₀ ⊗ b₂) ⊕ (a₁ ⊗ b₁)) ⊕ (a₂ ⊗ b₀)
    s₃ = (((a₀ ⊗ b₃) ⊕ (a₁ ⊗ b₂)) ⊕ (a₂ ⊗ b₁)) ⊕ (a₃ ⊗ b₀)
    s₄ = ((a₁ ⊗ b₃) ⊕ (a₂ ⊗ b₂)) ⊕ (a₃ ⊗ b₁)
    s₅ = (a₂ ⊗ b₃) ⊕ (a₃ ⊗ b₂)
    s₆ = a₃ ⊗ b₃

  add : Q⁴ A → Q⁴ A → Q⁴ A
  add (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃) =
    a₀ ⊕ b₀ , a₁ ⊕ b₁ , a₂ ⊕ b₂ , a₃ ⊕ b₃

------------------------------------------------------------------------
-- Elements: c₀ + c₁ x + c₂ x² + c₃ x³

-- A data type, not a record: with eta, a product of variables would
-- unfold into its integer components whenever two products are
-- compared, and nested products blow up.
data Q : Set where
  ⟨_,_,_,_⟩ : ℤ → ℤ → ℤ → ℤ → Q

c₀ c₁ c₂ c₃ : Q → ℤ
c₀ ⟨ a , _ , _ , _ ⟩ = a
c₁ ⟨ _ , a , _ , _ ⟩ = a
c₂ ⟨ _ , _ , a , _ ⟩ = a
c₃ ⟨ _ , _ , _ , a ⟩ = a

private
  open module MZ = Mul ℤ._+_ ℤ._*_ p q using ()

  from : Q⁴ ℤ → Q
  from (a₀ , a₁ , a₂ , a₃) = ⟨ a₀ , a₁ , a₂ , a₃ ⟩

infixl 6 _+_
infixl 7 _*_ _*ₗ_
infix  8 -_

-- Both arguments are matched on, so that a product of variables does
-- not reduce.  _*ₗ_ is the product as the solver sees it.
_+_ _*ₗ_ : Q → Q → Q
⟨ a₀ , a₁ , a₂ , a₃ ⟩ + ⟨ b₀ , b₁ , b₂ , b₃ ⟩ = from (MZ.add (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃))
⟨ a₀ , a₁ , a₂ , a₃ ⟩ *ₗ ⟨ b₀ , b₁ , b₂ , b₃ ⟩ = from (MZ.mul (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃))

-- Forcing an integer to normal form before passing it on.
forceℕ : {A : Set} → ℕ → (ℕ → A) → A
forceℕ zero    k = k zero
forceℕ (suc m) k = k (suc m)

forceℤ : {A : Set} → ℤ → (ℤ → A) → A
forceℤ (+ n)    k = forceℕ n (λ m → k (+ m))
forceℤ -[1+ n ] k = forceℕ n (λ m → k -[1+ m ])

forceℤ-id : {A : Set} (i : ℤ) (k : ℤ → A) → forceℤ i k ≡ k i
forceℤ-id (+ zero)        k = refl
forceℤ-id (+ suc n)       k = refl
forceℤ-id -[1+ zero ]     k = refl
forceℤ-id -[1+ suc n ]    k = refl

-- The product used for evaluation: _*ₗ_ on normalised coefficients.
-- Each coefficient of a factor occurs in several of the product's, and
-- the evaluator does not share them: without the forcing, a chain of
-- products, such as ζ¹² or a long circuit's matrix, re-evaluates its
-- earlier factors exponentially often.
_*_ : Q → Q → Q
⟨ a₀ , a₁ , a₂ , a₃ ⟩ * ⟨ b₀ , b₁ , b₂ , b₃ ⟩ =
  forceℤ a₀ λ a₀ → forceℤ a₁ λ a₁ → forceℤ a₂ λ a₂ → forceℤ a₃ λ a₃ →
  forceℤ b₀ λ b₀ → forceℤ b₁ λ b₁ → forceℤ b₂ λ b₂ → forceℤ b₃ λ b₃ →
  ⟨ a₀ , a₁ , a₂ , a₃ ⟩ *ₗ ⟨ b₀ , b₁ , b₂ , b₃ ⟩

*≡*ₗ : ∀ a b → a * b ≡ a *ₗ b
*≡*ₗ ⟨ a₀ , a₁ , a₂ , a₃ ⟩ ⟨ b₀ , b₁ , b₂ , b₃ ⟩ =
  Eq.trans (forceℤ-id a₀ _) (Eq.trans (forceℤ-id a₁ _)
  (Eq.trans (forceℤ-id a₂ _) (Eq.trans (forceℤ-id a₃ _)
  (Eq.trans (forceℤ-id b₀ _) (Eq.trans (forceℤ-id b₁ _)
  (Eq.trans (forceℤ-id b₂ _) (forceℤ-id b₃ _)))))))

-_ : Q → Q
- ⟨ a₀ , a₁ , a₂ , a₃ ⟩ = ⟨ ℤ.- a₀ , ℤ.- a₁ , ℤ.- a₂ , ℤ.- a₃ ⟩

0q 1q x : Q
0q = ⟨ + 0 , + 0 , + 0 , + 0 ⟩
1q = ⟨ + 1 , + 0 , + 0 , + 0 ⟩
x  = ⟨ + 0 , + 1 , + 0 , + 0 ⟩

-- The integers.
ι : ℤ → Q
ι a = ⟨ a , + 0 , + 0 , + 0 ⟩

infixr 8 _^_
_^_ : Q → ℕ → Q
a ^ zero  = 1q
a ^ suc k = a * a ^ k

------------------------------------------------------------------------
-- Equality

infix 4 _≟_
_≟_ : DecidableEquality Q
⟨ a₀ , a₁ , a₂ , a₃ ⟩ ≟ ⟨ b₀ , b₁ , b₂ , b₃ ⟩
  with a₀ ℤP.≟ b₀ | a₁ ℤP.≟ b₁ | a₂ ℤP.≟ b₂ | a₃ ℤP.≟ b₃
... | yes refl | yes refl | yes refl | yes refl = yes refl
... | no ne | _ | _ | _ = no λ e → ne (Eq.cong c₀ e)
... | yes _ | no ne | _ | _ = no λ e → ne (Eq.cong c₁ e)
... | yes _ | yes _ | no ne | _ = no λ e → ne (Eq.cong c₂ e)
... | yes _ | yes _ | yes _ | no ne = no λ e → ne (Eq.cong c₃ e)

-- Equal components make equal elements.
⟨≡⟩ : ∀ {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃} →
      a₀ ≡ b₀ → a₁ ≡ b₁ → a₂ ≡ b₂ → a₃ ≡ b₃ →
      ⟨ a₀ , a₁ , a₂ , a₃ ⟩ ≡ ⟨ b₀ , b₁ , b₂ , b₃ ⟩
⟨≡⟩ refl refl refl refl = refl

------------------------------------------------------------------------
-- The ring laws

private
  module MP {n : ℕ} = Mul (_:+_ {n}) _:*_

  -- The four components of a quadruple of polynomials.
  π₀ π₁ π₂ π₃ : {B : Set} → Q⁴ B → B
  π₀ (a , _ , _ , _) = a
  π₁ (_ , a , _ , _) = a
  π₂ (_ , _ , a , _) = a
  π₃ (_ , _ , _ , a) = a

  +-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  +-assoc ⟨ a₀ , a₁ , a₂ , a₃ ⟩ ⟨ b₀ , b₁ , b₂ , b₃ ⟩ ⟨ c₀ , c₁ , c₂ , c₃ ⟩ =
    ⟨≡⟩ (ℤP.+-assoc a₀ b₀ c₀) (ℤP.+-assoc a₁ b₁ c₁)
        (ℤP.+-assoc a₂ b₂ c₂) (ℤP.+-assoc a₃ b₃ c₃)

  +-comm : ∀ a b → a + b ≡ b + a
  +-comm ⟨ a₀ , a₁ , a₂ , a₃ ⟩ ⟨ b₀ , b₁ , b₂ , b₃ ⟩ =
    ⟨≡⟩ (ℤP.+-comm a₀ b₀) (ℤP.+-comm a₁ b₁) (ℤP.+-comm a₂ b₂) (ℤP.+-comm a₃ b₃)

  +-identityˡ : ∀ a → 0q + a ≡ a
  +-identityˡ ⟨ a₀ , a₁ , a₂ , a₃ ⟩ =
    ⟨≡⟩ (ℤP.+-identityˡ a₀) (ℤP.+-identityˡ a₁)
        (ℤP.+-identityˡ a₂) (ℤP.+-identityˡ a₃)

  +-identityʳ : ∀ a → a + 0q ≡ a
  +-identityʳ ⟨ a₀ , a₁ , a₂ , a₃ ⟩ =
    ⟨≡⟩ (ℤP.+-identityʳ a₀) (ℤP.+-identityʳ a₁)
        (ℤP.+-identityʳ a₂) (ℤP.+-identityʳ a₃)

  -‿inverseˡ : ∀ a → - a + a ≡ 0q
  -‿inverseˡ ⟨ a₀ , a₁ , a₂ , a₃ ⟩ =
    ⟨≡⟩ (ℤP.+-inverseˡ a₀) (ℤP.+-inverseˡ a₁)
        (ℤP.+-inverseˡ a₂) (ℤP.+-inverseˡ a₃)

  -‿inverseʳ : ∀ a → a + - a ≡ 0q
  -‿inverseʳ ⟨ a₀ , a₁ , a₂ , a₃ ⟩ =
    ⟨≡⟩ (ℤP.+-inverseʳ a₀) (ℤP.+-inverseʳ a₁)
        (ℤP.+-inverseʳ a₂) (ℤP.+-inverseʳ a₃)

  *ₗ-comm : ∀ a b → a *ₗ b ≡ b *ₗ a
  *ₗ-comm ⟨ a₀ , a₁ , a₂ , a₃ ⟩ ⟨ b₀ , b₁ , b₂ , b₃ ⟩ =
    ⟨≡⟩ (solve 10 (λ p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
           π₀ (MP.mul p q (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃)) :=
           π₀ (MP.mul p q (b₀ , b₁ , b₂ , b₃) (a₀ , a₁ , a₂ , a₃)))
           refl p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
        (solve 10 (λ p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
           π₁ (MP.mul p q (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃)) :=
           π₁ (MP.mul p q (b₀ , b₁ , b₂ , b₃) (a₀ , a₁ , a₂ , a₃)))
           refl p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
        (solve 10 (λ p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
           π₂ (MP.mul p q (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃)) :=
           π₂ (MP.mul p q (b₀ , b₁ , b₂ , b₃) (a₀ , a₁ , a₂ , a₃)))
           refl p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
        (solve 10 (λ p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
           π₃ (MP.mul p q (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃)) :=
           π₃ (MP.mul p q (b₀ , b₁ , b₂ , b₃) (a₀ , a₁ , a₂ , a₃)))
           refl p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)

  *ₗ-identityˡ : ∀ a → 1q *ₗ a ≡ a
  *ₗ-identityˡ ⟨ a₀ , a₁ , a₂ , a₃ ⟩ =
    ⟨≡⟩ (solve 6 (λ p q a₀ a₁ a₂ a₃ →
           π₀ (MP.mul p q (con (+ 1) , con (+ 0) , con (+ 0) , con (+ 0))
                          (a₀ , a₁ , a₂ , a₃)) := a₀)
           refl p q a₀ a₁ a₂ a₃)
        (solve 6 (λ p q a₀ a₁ a₂ a₃ →
           π₁ (MP.mul p q (con (+ 1) , con (+ 0) , con (+ 0) , con (+ 0))
                          (a₀ , a₁ , a₂ , a₃)) := a₁)
           refl p q a₀ a₁ a₂ a₃)
        (solve 6 (λ p q a₀ a₁ a₂ a₃ →
           π₂ (MP.mul p q (con (+ 1) , con (+ 0) , con (+ 0) , con (+ 0))
                          (a₀ , a₁ , a₂ , a₃)) := a₂)
           refl p q a₀ a₁ a₂ a₃)
        (solve 6 (λ p q a₀ a₁ a₂ a₃ →
           π₃ (MP.mul p q (con (+ 1) , con (+ 0) , con (+ 0) , con (+ 0))
                          (a₀ , a₁ , a₂ , a₃)) := a₃)
           refl p q a₀ a₁ a₂ a₃)

  distribₗˡ : ∀ a b c → a *ₗ (b + c) ≡ a *ₗ b + a *ₗ c
  distribₗˡ ⟨ a₀ , a₁ , a₂ , a₃ ⟩ ⟨ b₀ , b₁ , b₂ , b₃ ⟩ ⟨ c₀ , c₁ , c₂ , c₃ ⟩ =
    ⟨≡⟩ (solve 14 (λ p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ →
           π₀ (MP.mul p q (a₀ , a₁ , a₂ , a₃)
                 (MP.add p q (b₀ , b₁ , b₂ , b₃) (c₀ , c₁ , c₂ , c₃))) :=
           π₀ (MP.add p q (MP.mul p q (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃))
                          (MP.mul p q (a₀ , a₁ , a₂ , a₃) (c₀ , c₁ , c₂ , c₃))))
           refl p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃)
        (solve 14 (λ p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ →
           π₁ (MP.mul p q (a₀ , a₁ , a₂ , a₃)
                 (MP.add p q (b₀ , b₁ , b₂ , b₃) (c₀ , c₁ , c₂ , c₃))) :=
           π₁ (MP.add p q (MP.mul p q (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃))
                          (MP.mul p q (a₀ , a₁ , a₂ , a₃) (c₀ , c₁ , c₂ , c₃))))
           refl p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃)
        (solve 14 (λ p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ →
           π₂ (MP.mul p q (a₀ , a₁ , a₂ , a₃)
                 (MP.add p q (b₀ , b₁ , b₂ , b₃) (c₀ , c₁ , c₂ , c₃))) :=
           π₂ (MP.add p q (MP.mul p q (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃))
                          (MP.mul p q (a₀ , a₁ , a₂ , a₃) (c₀ , c₁ , c₂ , c₃))))
           refl p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃)
        (solve 14 (λ p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ →
           π₃ (MP.mul p q (a₀ , a₁ , a₂ , a₃)
                 (MP.add p q (b₀ , b₁ , b₂ , b₃) (c₀ , c₁ , c₂ , c₃))) :=
           π₃ (MP.add p q (MP.mul p q (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃))
                          (MP.mul p q (a₀ , a₁ , a₂ , a₃) (c₀ , c₁ , c₂ , c₃))))
           refl p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃)

  *ₗ-assoc : ∀ a b c → (a *ₗ b) *ₗ c ≡ a *ₗ (b *ₗ c)
  *ₗ-assoc ⟨ a₀ , a₁ , a₂ , a₃ ⟩ ⟨ b₀ , b₁ , b₂ , b₃ ⟩ ⟨ c₀ , c₁ , c₂ , c₃ ⟩ =
    ⟨≡⟩ (solve 14 (λ p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ →
           π₀ (MP.mul p q (MP.mul p q (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃))
                          (c₀ , c₁ , c₂ , c₃)) :=
           π₀ (MP.mul p q (a₀ , a₁ , a₂ , a₃)
                          (MP.mul p q (b₀ , b₁ , b₂ , b₃) (c₀ , c₁ , c₂ , c₃))))
           refl p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃)
        (solve 14 (λ p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ →
           π₁ (MP.mul p q (MP.mul p q (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃))
                          (c₀ , c₁ , c₂ , c₃)) :=
           π₁ (MP.mul p q (a₀ , a₁ , a₂ , a₃)
                          (MP.mul p q (b₀ , b₁ , b₂ , b₃) (c₀ , c₁ , c₂ , c₃))))
           refl p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃)
        (solve 14 (λ p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ →
           π₂ (MP.mul p q (MP.mul p q (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃))
                          (c₀ , c₁ , c₂ , c₃)) :=
           π₂ (MP.mul p q (a₀ , a₁ , a₂ , a₃)
                          (MP.mul p q (b₀ , b₁ , b₂ , b₃) (c₀ , c₁ , c₂ , c₃))))
           refl p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃)
        (solve 14 (λ p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ →
           π₃ (MP.mul p q (MP.mul p q (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃))
                          (c₀ , c₁ , c₂ , c₃)) :=
           π₃ (MP.mul p q (a₀ , a₁ , a₂ , a₃)
                          (MP.mul p q (b₀ , b₁ , b₂ , b₃) (c₀ , c₁ , c₂ , c₃))))
           refl p q a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃)

-- The laws of the evaluated product, through *≡*ₗ.
private
  *-comm : ∀ a b → a * b ≡ b * a
  *-comm a b = Eq.trans (*≡*ₗ a b) (Eq.trans (*ₗ-comm a b) (Eq.sym (*≡*ₗ b a)))

  *-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
  *-assoc a b c =
    Eq.trans (Eq.cong (_* c) (*≡*ₗ a b))
    (Eq.trans (*≡*ₗ (a *ₗ b) c)
    (Eq.trans (*ₗ-assoc a b c)
    (Eq.trans (Eq.sym (*≡*ₗ a (b *ₗ c)))
              (Eq.cong (a *_) (Eq.sym (*≡*ₗ b c))))))

  *-identityˡ : ∀ a → 1q * a ≡ a
  *-identityˡ a = Eq.trans (*≡*ₗ 1q a) (*ₗ-identityˡ a)

  *-identityʳ : ∀ a → a * 1q ≡ a
  *-identityʳ a = Eq.trans (*-comm a 1q) (*-identityˡ a)

  distribˡ : ∀ a b c → a * (b + c) ≡ a * b + a * c
  distribˡ a b c =
    Eq.trans (*≡*ₗ a (b + c))
      (Eq.trans (distribₗˡ a b c)
                (Eq.cong₂ _+_ (Eq.sym (*≡*ₗ a b)) (Eq.sym (*≡*ₗ a c))))

  distribʳ : ∀ a b c → (b + c) * a ≡ b * a + c * a
  distribʳ a b c =
    Eq.trans (*-comm (b + c) a)
      (Eq.trans (distribˡ a b c) (Eq.cong₂ _+_ (*-comm a b) (*-comm a c)))

isCommutativeRing : IsCommutativeRing _≡_ _+_ _*_ -_ 0q 1q
isCommutativeRing = record
  { isRing = record
    { +-isAbelianGroup = record
      { isGroup = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = Eq.isEquivalence ; ∙-cong = Eq.cong₂ _+_ }
            ; assoc = +-assoc }
          ; identity = +-identityˡ , +-identityʳ }
        ; inverse = -‿inverseˡ , -‿inverseʳ
        ; ⁻¹-cong = Eq.cong -_ }
      ; comm = +-comm }
    ; *-cong = Eq.cong₂ _*_
    ; *-assoc = *-assoc
    ; *-identity = *-identityˡ , *-identityʳ
    ; distrib = distribˡ , distribʳ }
  ; *-comm = *-comm }

commutativeRing : CommutativeRing 0ℓ 0ℓ
commutativeRing = record { isCommutativeRing = isCommutativeRing }

------------------------------------------------------------------------
-- Cancelling a square root of a nonzero integer

private
  ι-* : ∀ d a → ι d *ₗ a ≡ ⟨ d ℤ.* c₀ a , d ℤ.* c₁ a , d ℤ.* c₂ a , d ℤ.* c₃ a ⟩
  ι-* d ⟨ a₀ , a₁ , a₂ , a₃ ⟩ =
    ⟨≡⟩ (solve 7 (λ p q d a₀ a₁ a₂ a₃ →
           π₀ (MP.mul p q (d , con (+ 0) , con (+ 0) , con (+ 0)) (a₀ , a₁ , a₂ , a₃))
           := d :* a₀)
           refl p q d a₀ a₁ a₂ a₃)
        (solve 7 (λ p q d a₀ a₁ a₂ a₃ →
           π₁ (MP.mul p q (d , con (+ 0) , con (+ 0) , con (+ 0)) (a₀ , a₁ , a₂ , a₃))
           := d :* a₁)
           refl p q d a₀ a₁ a₂ a₃)
        (solve 7 (λ p q d a₀ a₁ a₂ a₃ →
           π₂ (MP.mul p q (d , con (+ 0) , con (+ 0) , con (+ 0)) (a₀ , a₁ , a₂ , a₃))
           := d :* a₂)
           refl p q d a₀ a₁ a₂ a₃)
        (solve 7 (λ p q d a₀ a₁ a₂ a₃ →
           π₃ (MP.mul p q (d , con (+ 0) , con (+ 0) , con (+ 0)) (a₀ , a₁ , a₂ , a₃))
           := d :* a₃)
           refl p q d a₀ a₁ a₂ a₃)

-- If r r is a nonzero integer d, multiplication by r is injective.
cancel : (r : Q) (d : ℤ) .{{_ : ℤ.NonZero d}} → r * r ≡ ι d →
         ∀ {a b} → r * a ≡ r * b → a ≡ b
cancel r d rr {a@(⟨ _ , _ , _ , _ ⟩)} {b@(⟨ _ , _ , _ , _ ⟩)} e =
  ⟨≡⟩ (ℤP.*-cancelˡ-≡ d _ _ (Eq.cong c₀ dd)) (ℤP.*-cancelˡ-≡ d _ _ (Eq.cong c₁ dd))
      (ℤP.*-cancelˡ-≡ d _ _ (Eq.cong c₂ dd)) (ℤP.*-cancelˡ-≡ d _ _ (Eq.cong c₃ dd))
  where
  da≡db : ι d * a ≡ ι d * b
  da≡db = begin
    ι d * a        ≡⟨ Eq.cong (_* a) (Eq.sym rr) ⟩
    (r * r) * a    ≡⟨ *-assoc r r a ⟩
    r * (r * a)    ≡⟨ Eq.cong (r *_) e ⟩
    r * (r * b)    ≡⟨ Eq.sym (*-assoc r r b) ⟩
    (r * r) * b    ≡⟨ Eq.cong (_* b) rr ⟩
    ι d * b        ∎
    where open Eq.≡-Reasoning

  dd : ⟨ d ℤ.* c₀ a , d ℤ.* c₁ a , d ℤ.* c₂ a , d ℤ.* c₃ a ⟩ ≡
       ⟨ d ℤ.* c₀ b , d ℤ.* c₁ b , d ℤ.* c₂ b , d ℤ.* c₃ b ⟩
  dd = Eq.trans (Eq.sym (ι-* d a))
         (Eq.trans (Eq.sym (*≡*ₗ (ι d) a)) (Eq.trans da≡db (Eq.trans (*≡*ₗ (ι d) b) (ι-* d b))))

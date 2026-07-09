------------------------------------------------------------------------
-- Presentations of groups
--
-- Semantics of the symmetric group: permutations of Fin n.
------------------------------------------------------------------------

{-# OPTIONS  --safe #-}

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ ; zero ; suc)
import Data.Integer as Int
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Notations using (₁₊ ; ₂₊)
open import Word.Base using (Word ; ε)

open import Algebra.Bundles using (Group)
open import Algebra.Definitions using (LeftInverse ; RightInverse)
open import Algebra.Structures using (IsGroup)
import Data.Integer.Properties as IntP
open import Data.Product using (_,_)
open import Level using (0ℓ)

open import Data.Unit using (tt)

module Examples.Groups.Cyclic.Semantics where

open import Examples.Groups.Cyclic.Normalization

open import Zp.ModularArithmetic
------------------------------------------------------------------------
-- 

Cn : ℕ → Set
Cn 0 = Int.ℤ
Cn n = ℤ n

------------------------------------------------------------------------
-- The carrier Cn n is a group under addition

-- For N = 0 the carrier is ℤ, whose additive group is the standard-
-- library one.
Cn0-isGroup : IsGroup (_≡_ {A = Cn 0}) Int._+_ (Int.+ 0) (Int.-_)
Cn0-isGroup = IntP.+-0-isGroup

Cn0-group : Group 0ℓ 0ℓ
Cn0-group = record
  { Carrier = Cn 0
  ; _≈_     = _≡_
  ; _∙_     = Int._+_
  ; ε       = Int.+ 0
  ; _⁻¹     = Int.-_
  ; isGroup = Cn0-isGroup
  }

-- For N = suc n the carrier is ℤ/(suc n)ℤ.  ModularArithmetic supplies
-- the abelian-group structure for moduli ≥ 2; the inverse law for the
-- trivial modulus 1 (ℤ/1ℤ, a singleton) is added here so that the
-- structure is available for every suc n.
+-inverseˡ' : ∀ {n} → LeftInverse (_≡_ {A = ℤ (₁₊ n)}) ₀ (-_) _+_
+-inverseˡ' {zero}  zero = refl
+-inverseˡ' {suc m}      = +-inverseˡ {m}

+-inverseʳ' : ∀ {n} → RightInverse (_≡_ {A = ℤ (₁₊ n)}) ₀ (-_) _+_
+-inverseʳ' {zero}  zero = refl
+-inverseʳ' {suc m}      = +-inverseʳ {m}

Cn-suc-isGroup : ∀ {n} → IsGroup (_≡_ {A = Cn (suc n)}) _+_ ₀ (-_)
Cn-suc-isGroup {n} = record
  { isMonoid = record
      { isSemigroup = record
          { isMagma = record
              { isEquivalence = Eq.isEquivalence
              ; ∙-cong        = +-cong
              }
          ; assoc = +-assoc
          }
      ; identity = +-identity
      }
  ; inverse = +-inverseˡ' , +-inverseʳ'
  ; ⁻¹-cong = neg-cong
  }

Cn-suc-group : ∀ {n} → Group 0ℓ 0ℓ
Cn-suc-group {n} = record
  { Carrier = Cn (suc n)
  ; _≈_     = _≡_
  ; _∙_     = _+_
  ; ε       = ₀
  ; _⁻¹     = -_
  ; isGroup = Cn-suc-isGroup
  }

-- The ℕ-indexed family of additive groups: ℤ at 0, ℤ/Nℤ at N = suc _.
Cn-group : ℕ → Group 0ℓ 0ℓ
Cn-group zero    = Cn0-group
Cn-group (suc n) = Cn-suc-group {n}



gg : ∀ {n} -> X -> Cn n
gg {₀} tt = Int.+ 1
gg {₁} tt = ₀
gg {₂₊ n} tt = ₁

⟦_⟧₀ = gg

-- The denotation is the monoid homomorphism out of the free monoid
-- sending the generator to gg.  Extend is lifted to these top-level
-- modules rather than kept in a where-block, so that ⟦_⟧ computes and
-- its homomorphism laws (homo, ε-homo) are in scope.  The n-split keeps
-- the codomain Cn n reducing (Cn-group 0 = ℤ, Cn-group (suc _) =
-- ℤ/(suc _)ℤ), so the monoid carrier matches Cn n on the nose.
module Interp0 where
  open import Normalization.StarInterp (0 Cn,_===_)
  open Extend (Group.monoid (Cn-group 0)) (gg {0}) public

module Interpₛ (n' : ℕ) where
  open import Normalization.StarInterp (suc n' Cn,_===_)
  open Extend (Group.monoid (Cn-group (suc n'))) (gg {suc n'}) public

⟦_⟧ : ∀ {n} → Word X → Cn n
⟦_⟧ {0}      = Interp0.⟦_⟧
⟦_⟧ {suc n'} = Interpₛ.⟦_⟧ n'

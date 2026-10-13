------------------------------------------------------------------------
-- Presentations of groups
--
-- Arithmetic modulo 3
--
-- The phases ω^σ of qutrit Pauli operators, the exponents of X and Z,
-- and the digits of basis vectors are elements of ℤ/3, here Fin 3 with
-- addition and multiplication by tables.  The laws are checked case by
-- case (the module is generated: scratchpad qt/gen_z3.pl).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Qutrit-Clifford.Z3 where

open import Data.Fin.Base using (Fin ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; sym ; cong)

Z3 : Set
Z3 = Fin 3

pattern 𝟎 = zero
pattern 𝟏 = suc zero
pattern 𝟐 = suc (suc zero)

infixl 6 _⊞_
infixl 7 _⊠_
infix  8 ⊟_

_⊞_ : Z3 → Z3 → Z3
𝟎 ⊞ 𝟎 = 𝟎
𝟎 ⊞ 𝟏 = 𝟏
𝟎 ⊞ 𝟐 = 𝟐
𝟏 ⊞ 𝟎 = 𝟏
𝟏 ⊞ 𝟏 = 𝟐
𝟏 ⊞ 𝟐 = 𝟎
𝟐 ⊞ 𝟎 = 𝟐
𝟐 ⊞ 𝟏 = 𝟎
𝟐 ⊞ 𝟐 = 𝟏

_⊠_ : Z3 → Z3 → Z3
𝟎 ⊠ 𝟎 = 𝟎
𝟎 ⊠ 𝟏 = 𝟎
𝟎 ⊠ 𝟐 = 𝟎
𝟏 ⊠ 𝟎 = 𝟎
𝟏 ⊠ 𝟏 = 𝟏
𝟏 ⊠ 𝟐 = 𝟐
𝟐 ⊠ 𝟎 = 𝟎
𝟐 ⊠ 𝟏 = 𝟐
𝟐 ⊠ 𝟐 = 𝟏

⊟_ : Z3 → Z3
⊟ 𝟎 = 𝟎
⊟ 𝟏 = 𝟐
⊟ 𝟐 = 𝟏

⊞-identityʳ : ∀ a → a ⊞ 𝟎 ≡ a
⊞-identityʳ 𝟎 = refl
⊞-identityʳ 𝟏 = refl
⊞-identityʳ 𝟐 = refl

⊞-identityˡ : ∀ a → 𝟎 ⊞ a ≡ a
⊞-identityˡ 𝟎 = refl
⊞-identityˡ 𝟏 = refl
⊞-identityˡ 𝟐 = refl

⊞-inverseʳ : ∀ a → a ⊞ ⊟ a ≡ 𝟎
⊞-inverseʳ 𝟎 = refl
⊞-inverseʳ 𝟏 = refl
⊞-inverseʳ 𝟐 = refl

⊟-twice : ∀ a → 𝟐 ⊠ a ≡ ⊟ a
⊟-twice 𝟎 = refl
⊟-twice 𝟏 = refl
⊟-twice 𝟐 = refl

⊠-one : ∀ a → 𝟏 ⊠ a ≡ a
⊠-one 𝟎 = refl
⊠-one 𝟏 = refl
⊠-one 𝟐 = refl

⊞-comm : ∀ a b → a ⊞ b ≡ b ⊞ a
⊞-comm 𝟎 𝟎 = refl
⊞-comm 𝟎 𝟏 = refl
⊞-comm 𝟎 𝟐 = refl
⊞-comm 𝟏 𝟎 = refl
⊞-comm 𝟏 𝟏 = refl
⊞-comm 𝟏 𝟐 = refl
⊞-comm 𝟐 𝟎 = refl
⊞-comm 𝟐 𝟏 = refl
⊞-comm 𝟐 𝟐 = refl

⊠-comm : ∀ a b → a ⊠ b ≡ b ⊠ a
⊠-comm 𝟎 𝟎 = refl
⊠-comm 𝟎 𝟏 = refl
⊠-comm 𝟎 𝟐 = refl
⊠-comm 𝟏 𝟎 = refl
⊠-comm 𝟏 𝟏 = refl
⊠-comm 𝟏 𝟐 = refl
⊠-comm 𝟐 𝟎 = refl
⊠-comm 𝟐 𝟏 = refl
⊠-comm 𝟐 𝟐 = refl

⊞-cancelʳ : ∀ a b → a ⊞ b ⊞ ⊟ b ≡ a
⊞-cancelʳ 𝟎 𝟎 = refl
⊞-cancelʳ 𝟎 𝟏 = refl
⊞-cancelʳ 𝟎 𝟐 = refl
⊞-cancelʳ 𝟏 𝟎 = refl
⊞-cancelʳ 𝟏 𝟏 = refl
⊞-cancelʳ 𝟏 𝟐 = refl
⊞-cancelʳ 𝟐 𝟎 = refl
⊞-cancelʳ 𝟐 𝟏 = refl
⊞-cancelʳ 𝟐 𝟐 = refl

⊟-⊞ : ∀ a b → ⊟ (a ⊞ b) ≡ ⊟ a ⊞ ⊟ b
⊟-⊞ 𝟎 𝟎 = refl
⊟-⊞ 𝟎 𝟏 = refl
⊟-⊞ 𝟎 𝟐 = refl
⊟-⊞ 𝟏 𝟎 = refl
⊟-⊞ 𝟏 𝟏 = refl
⊟-⊞ 𝟏 𝟐 = refl
⊟-⊞ 𝟐 𝟎 = refl
⊟-⊞ 𝟐 𝟏 = refl
⊟-⊞ 𝟐 𝟐 = refl

⊟-⊠ : ∀ a b → ⊟ (a ⊠ b) ≡ ⊟ a ⊠ b
⊟-⊠ 𝟎 𝟎 = refl
⊟-⊠ 𝟎 𝟏 = refl
⊟-⊠ 𝟎 𝟐 = refl
⊟-⊠ 𝟏 𝟎 = refl
⊟-⊠ 𝟏 𝟏 = refl
⊟-⊠ 𝟏 𝟐 = refl
⊟-⊠ 𝟐 𝟎 = refl
⊟-⊠ 𝟐 𝟏 = refl
⊟-⊠ 𝟐 𝟐 = refl

⊞-assoc : ∀ a b c → a ⊞ b ⊞ c ≡ a ⊞ (b ⊞ c)
⊞-assoc 𝟎 𝟎 𝟎 = refl
⊞-assoc 𝟎 𝟎 𝟏 = refl
⊞-assoc 𝟎 𝟎 𝟐 = refl
⊞-assoc 𝟎 𝟏 𝟎 = refl
⊞-assoc 𝟎 𝟏 𝟏 = refl
⊞-assoc 𝟎 𝟏 𝟐 = refl
⊞-assoc 𝟎 𝟐 𝟎 = refl
⊞-assoc 𝟎 𝟐 𝟏 = refl
⊞-assoc 𝟎 𝟐 𝟐 = refl
⊞-assoc 𝟏 𝟎 𝟎 = refl
⊞-assoc 𝟏 𝟎 𝟏 = refl
⊞-assoc 𝟏 𝟎 𝟐 = refl
⊞-assoc 𝟏 𝟏 𝟎 = refl
⊞-assoc 𝟏 𝟏 𝟏 = refl
⊞-assoc 𝟏 𝟏 𝟐 = refl
⊞-assoc 𝟏 𝟐 𝟎 = refl
⊞-assoc 𝟏 𝟐 𝟏 = refl
⊞-assoc 𝟏 𝟐 𝟐 = refl
⊞-assoc 𝟐 𝟎 𝟎 = refl
⊞-assoc 𝟐 𝟎 𝟏 = refl
⊞-assoc 𝟐 𝟎 𝟐 = refl
⊞-assoc 𝟐 𝟏 𝟎 = refl
⊞-assoc 𝟐 𝟏 𝟏 = refl
⊞-assoc 𝟐 𝟏 𝟐 = refl
⊞-assoc 𝟐 𝟐 𝟎 = refl
⊞-assoc 𝟐 𝟐 𝟏 = refl
⊞-assoc 𝟐 𝟐 𝟐 = refl

⊠-assoc : ∀ a b c → a ⊠ b ⊠ c ≡ a ⊠ (b ⊠ c)
⊠-assoc 𝟎 𝟎 𝟎 = refl
⊠-assoc 𝟎 𝟎 𝟏 = refl
⊠-assoc 𝟎 𝟎 𝟐 = refl
⊠-assoc 𝟎 𝟏 𝟎 = refl
⊠-assoc 𝟎 𝟏 𝟏 = refl
⊠-assoc 𝟎 𝟏 𝟐 = refl
⊠-assoc 𝟎 𝟐 𝟎 = refl
⊠-assoc 𝟎 𝟐 𝟏 = refl
⊠-assoc 𝟎 𝟐 𝟐 = refl
⊠-assoc 𝟏 𝟎 𝟎 = refl
⊠-assoc 𝟏 𝟎 𝟏 = refl
⊠-assoc 𝟏 𝟎 𝟐 = refl
⊠-assoc 𝟏 𝟏 𝟎 = refl
⊠-assoc 𝟏 𝟏 𝟏 = refl
⊠-assoc 𝟏 𝟏 𝟐 = refl
⊠-assoc 𝟏 𝟐 𝟎 = refl
⊠-assoc 𝟏 𝟐 𝟏 = refl
⊠-assoc 𝟏 𝟐 𝟐 = refl
⊠-assoc 𝟐 𝟎 𝟎 = refl
⊠-assoc 𝟐 𝟎 𝟏 = refl
⊠-assoc 𝟐 𝟎 𝟐 = refl
⊠-assoc 𝟐 𝟏 𝟎 = refl
⊠-assoc 𝟐 𝟏 𝟏 = refl
⊠-assoc 𝟐 𝟏 𝟐 = refl
⊠-assoc 𝟐 𝟐 𝟎 = refl
⊠-assoc 𝟐 𝟐 𝟏 = refl
⊠-assoc 𝟐 𝟐 𝟐 = refl

⊠-distribˡ : ∀ a b c → a ⊠ (b ⊞ c) ≡ a ⊠ b ⊞ a ⊠ c
⊠-distribˡ 𝟎 𝟎 𝟎 = refl
⊠-distribˡ 𝟎 𝟎 𝟏 = refl
⊠-distribˡ 𝟎 𝟎 𝟐 = refl
⊠-distribˡ 𝟎 𝟏 𝟎 = refl
⊠-distribˡ 𝟎 𝟏 𝟏 = refl
⊠-distribˡ 𝟎 𝟏 𝟐 = refl
⊠-distribˡ 𝟎 𝟐 𝟎 = refl
⊠-distribˡ 𝟎 𝟐 𝟏 = refl
⊠-distribˡ 𝟎 𝟐 𝟐 = refl
⊠-distribˡ 𝟏 𝟎 𝟎 = refl
⊠-distribˡ 𝟏 𝟎 𝟏 = refl
⊠-distribˡ 𝟏 𝟎 𝟐 = refl
⊠-distribˡ 𝟏 𝟏 𝟎 = refl
⊠-distribˡ 𝟏 𝟏 𝟏 = refl
⊠-distribˡ 𝟏 𝟏 𝟐 = refl
⊠-distribˡ 𝟏 𝟐 𝟎 = refl
⊠-distribˡ 𝟏 𝟐 𝟏 = refl
⊠-distribˡ 𝟏 𝟐 𝟐 = refl
⊠-distribˡ 𝟐 𝟎 𝟎 = refl
⊠-distribˡ 𝟐 𝟎 𝟏 = refl
⊠-distribˡ 𝟐 𝟎 𝟐 = refl
⊠-distribˡ 𝟐 𝟏 𝟎 = refl
⊠-distribˡ 𝟐 𝟏 𝟏 = refl
⊠-distribˡ 𝟐 𝟏 𝟐 = refl
⊠-distribˡ 𝟐 𝟐 𝟎 = refl
⊠-distribˡ 𝟐 𝟐 𝟏 = refl
⊠-distribˡ 𝟐 𝟐 𝟐 = refl

-- Equal sums with a common summand have equal other summands.
⊞-cancel : ∀ a a' b → a ⊞ b ≡ a' ⊞ b → a ≡ a'
⊞-cancel a a' b e = trans (sym (⊞-cancelʳ a b)) (trans (cong (_⊞ ⊟ b) e) (⊞-cancelʳ a' b))

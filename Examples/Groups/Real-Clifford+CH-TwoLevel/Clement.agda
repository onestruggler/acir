------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément's relations for Uₙ(ℤ[1/√2]) = Oₙ(ℤ[1/√2]): equations (1)–(21)
-- of Definition 3.3 of A. Clément, "A complete set of relations for
-- the real Clifford+T group" (unfinished thesis, supervised by
-- N. J. Ross and P. Selinger, March 2019).
--
-- The generators are the paper's: (-1)_[j] is Z j, and H_[j,k],
-- X_[j,k].  Clément allows either order of the subscripts (Definition
-- 1.5, Remark 1.6): H_[k,j] for k > j is X_[j,k] H_[j,k] X_[j,k]
-- (Lemma 1.7, and his (22)) and X_[k,j] is X_[j,k]; these are the
-- words Hs and Xs of Symmetric, so each equation is stated for every
-- order of its indices, which need only be distinct as he writes them.
-- (22), the extra equation for n = 2, holds by definition in this
-- reading.  (20) and (21) are on the first four and six indices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Clement where

open import Data.Fin.Base using (Fin ; toℕ ; _<_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)

open import Word.Base
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric using (Hs ; Xs)

private
  variable
    n : ℕ
    j k l t : Fin n

------------------------------------------------------------------------
-- The words of (20) and (21)

module _ {n : ℕ} {i₀ i₁ i₂ i₃ : Fin n} (p01 : i₀ < i₁) (p02 : i₀ < i₂) (p13 : i₁ < i₃) where

  -- H_[0,1] H_[0,2] H_[1,3] H_[0,1] (-1)_[0] (-1)_[1] H_[0,2] H_[1,3]
  ⟨20⟩ˡ : Word (Gen n)
  ⟨20⟩ˡ = H i₀ i₁ p01 • H i₀ i₂ p02 • H i₁ i₃ p13 • H i₀ i₁ p01 • Z i₀ • Z i₁ •
          H i₀ i₂ p02 • H i₁ i₃ p13

  -- H_[0,2] H_[1,3] H_[0,1] (-1)_[0] (-1)_[1] H_[0,2] H_[1,3] H_[0,1]
  ⟨20⟩ʳ : Word (Gen n)
  ⟨20⟩ʳ = H i₀ i₂ p02 • H i₁ i₃ p13 • H i₀ i₁ p01 • Z i₀ • Z i₁ • H i₀ i₂ p02 •
          H i₁ i₃ p13 • H i₀ i₁ p01

module _ {n : ℕ} {i₀ i₁ i₂ i₃ i₄ i₅ : Fin n}
         (p01 : i₀ < i₁) (p02 : i₀ < i₂) (p13 : i₁ < i₃) (p04 : i₀ < i₄) (p15 : i₁ < i₅) where

  -- H_[0,1] H_[0,2] H_[1,3] H_[0,4] H_[1,5] H_[0,1] (-1)_[0] (-1)_[1]
  --   H_[0,4] H_[1,5] H_[0,2] H_[1,3]
  ⟨21⟩ˡ : Word (Gen n)
  ⟨21⟩ˡ = H i₀ i₁ p01 • H i₀ i₂ p02 • H i₁ i₃ p13 • H i₀ i₄ p04 • H i₁ i₅ p15 •
          H i₀ i₁ p01 • Z i₀ • Z i₁ • H i₀ i₄ p04 • H i₁ i₅ p15 • H i₀ i₂ p02 • H i₁ i₃ p13

  -- H_[0,2] H_[1,3] H_[0,4] H_[1,5] H_[0,1] (-1)_[0] (-1)_[1] H_[0,4]
  --   H_[1,5] H_[0,2] H_[1,3] H_[0,1]
  ⟨21⟩ʳ : Word (Gen n)
  ⟨21⟩ʳ = H i₀ i₂ p02 • H i₁ i₃ p13 • H i₀ i₄ p04 • H i₁ i₅ p15 • H i₀ i₁ p01 •
          Z i₀ • Z i₁ • H i₀ i₄ p04 • H i₁ i₅ p15 • H i₀ i₂ p02 • H i₁ i₃ p13 • H i₀ i₁ p01

------------------------------------------------------------------------
-- Definition 3.3

infix 4 _===ᶜ_

data _===ᶜ_ {n : ℕ} : WRel (Gen n) where
  -- (1)–(3)
  e1  : Z j • Z j ===ᶜ ε
  e2  : j ≢ k → Hs j k • Hs j k ===ᶜ ε
  e3  : j ≢ k → Xs j k • Xs j k ===ᶜ ε
  -- (4)–(9): disjoint generators commute.
  e4  : j ≢ k → Z j • Z k ===ᶜ Z k • Z j
  e5  : j ≢ k → l ≢ j → l ≢ k → Z l • Hs j k ===ᶜ Hs j k • Z l
  e6  : j ≢ k → l ≢ j → l ≢ k → Z l • Xs j k ===ᶜ Xs j k • Z l
  e7  : j ≢ k → l ≢ t → j ≢ l → j ≢ t → k ≢ l → k ≢ t →
        Hs j k • Hs l t ===ᶜ Hs l t • Hs j k
  e8  : j ≢ k → l ≢ t → j ≢ l → j ≢ t → k ≢ l → k ≢ t →
        Hs j k • Xs l t ===ᶜ Xs l t • Hs j k
  e9  : j ≢ k → l ≢ t → j ≢ l → j ≢ t → k ≢ l → k ≢ t →
        Xs j k • Xs l t ===ᶜ Xs l t • Xs j k
  -- (10)–(15): X_[j,k] swaps j and k.
  e10 : j ≢ k → Xs j k • Z k ===ᶜ Z j • Xs j k
  e11 : j ≢ k → Xs j k • Z j ===ᶜ Z k • Xs j k
  e12 : j ≢ k → j ≢ l → k ≢ l → Xs j k • Xs j l ===ᶜ Xs k l • Xs j k
  e13 : j ≢ k → l ≢ j → k ≢ l → Xs j k • Xs l j ===ᶜ Xs l k • Xs j k
  e14 : j ≢ k → j ≢ l → k ≢ l → Xs j k • Hs j l ===ᶜ Hs k l • Xs j k
  e15 : j ≢ k → l ≢ j → k ≢ l → Xs j k • Hs l j ===ᶜ Hs l k • Xs j k
  -- (16)–(18)
  e16 : j ≢ k → Z j • Z k • Xs j k ===ᶜ Xs j k • Z j • Z k
  e17 : j ≢ k → Z j • Z k • Hs j k ===ᶜ Hs j k • Z j • Z k
  e18 : j ≢ k → Hs j k • Xs j k ===ᶜ Z k • Hs j k
  -- (19), with j ≠ t (k = l is allowed, and trivial).
  e19 : j ≢ k → l ≢ t → j ≢ l → k ≢ t → j ≢ t →
        Hs j k • Hs l t • Hs j l • Hs k t ===ᶜ Hs j l • Hs k t • Hs j k • Hs l t
  -- (20), on the indices 0, 1, 2, 3.
  e20 : {i₀ i₁ i₂ i₃ : Fin n} → toℕ i₀ ≡ 0 → toℕ i₁ ≡ 1 → toℕ i₂ ≡ 2 → toℕ i₃ ≡ 3 →
        (p01 : i₀ < i₁) (p02 : i₀ < i₂) (p13 : i₁ < i₃) →
        ⟨20⟩ˡ p01 p02 p13 ===ᶜ ⟨20⟩ʳ p01 p02 p13
  -- (21), on the indices 0, …, 5.
  e21 : {i₀ i₁ i₂ i₃ i₄ i₅ : Fin n} →
        toℕ i₀ ≡ 0 → toℕ i₁ ≡ 1 → toℕ i₂ ≡ 2 → toℕ i₃ ≡ 3 → toℕ i₄ ≡ 4 → toℕ i₅ ≡ 5 →
        (p01 : i₀ < i₁) (p02 : i₀ < i₂) (p13 : i₁ < i₃) (p04 : i₀ < i₄) (p15 : i₁ < i₅) →
        ⟨21⟩ˡ p01 p02 p13 p04 p15 ===ᶜ ⟨21⟩ʳ p01 p02 p13 p04 p15

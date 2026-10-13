------------------------------------------------------------------------
-- Presentations of groups
--
-- The power-of-two dimensions used by the scaled presentation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Dimension where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _*_ ; _^_)
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong)

-- half n = 2^n - 1, without truncated subtraction in the proof.
half : ℕ → ℕ
half zero    = 0
half (suc n) = 2 ^ n + half n

half-correct : ∀ n → suc (half n) ≡ 2 ^ n
half-correct zero = refl
half-correct (suc n) =
  trans (sym (ℕP.+-suc (2 ^ n) (half n)))
    (trans (cong (2 ^ n +_) (half-correct n))
      (cong (2 ^ n +_) (sym (ℕP.+-identityʳ (2 ^ n)))))

-- The scaled theorem is indexed by k and has dimension (k+1)*2.
dimension : ∀ n → 2 ^ suc n ≡ suc (half n) * 2
dimension n =
  trans (ℕP.*-comm 2 (2 ^ n))
    (cong (_* 2) (sym (half-correct n)))

------------------------------------------------------------------------
-- Presentations of groups
--
-- Width-2 well-definedness pairs, assembled: with Strategy B armed at
-- width 2 (StrategyB2.wd-from-coset, via the completed width-1 tower),
-- each width-2 srel-wd obligation follows from its coset (≡) half
-- alone.  This module pairs the proved coset-half dispatchers with
-- wd-from-coset into full ≋ theorems — the width-2 instances of the
-- SrelWD holes for the sealed unary families.
--
-- (The kHn-heavy families (order-H/SH, comm-HHS) have per-branch coset
-- halves in PushWD but sealing their dispatchers blows up the checker;
-- they are assembled per-branch at their eventual fill sites.  The CZ
-- families' remaining coset halves are the parked engine cluster.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWD2
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Sum using (inj₁)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime using (C ; ract ; _≋_)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushWDM
  p-2 p-prime using (orderS-inj₁-coset ; semiMS-inj₁-coset ; Mmul-inj₁-coset-full)
import Examples.Groups.Symplectic.Normalization.Pushing.StrategyB2
  p-2 p-prime as SB2

------------------------------------------------------------------------
-- The sealed unary families at inj₁ cosets: full ≋ pairs at width 2.

order-S-wd2-inj₁ : ∀ (ml' : ML' 2) →
  (ract {1} ᵗ) (inj₁ ml') (S ^ p) ≋ (ract {1} ᵗ) (inj₁ ml') ε
order-S-wd2-inj₁ ml' =
  SB2.wd-from-coset (inj₁ ml') (srel Base.order-S) (orderS-inj₁-coset ml')

M-mul-wd2-inj₁ : ∀ (x* y* : ℤ* ₚ) (ml' : ML' 2) →
  (ract {1} ᵗ) (inj₁ ml') (ZM x* • ZM y*) ≋
  (ract {1} ᵗ) (inj₁ ml') (ZM (x* *' y*))
M-mul-wd2-inj₁ x* y* ml' =
  SB2.wd-from-coset (inj₁ ml') (srel (Base.M-mul x* y*))
    (Mmul-inj₁-coset-full x* y* ml')

semi-MS-wd2-inj₁ : ∀ (x* : ℤ* ₚ) (ml' : ML' 2) →
  (ract {1} ᵗ) (inj₁ ml') (ZM x* • S) ≋
  (ract {1} ᵗ) (inj₁ ml') (S^ (x* ^2) • ZM x*)
semi-MS-wd2-inj₁ x* ml' =
  SB2.wd-from-coset (inj₁ ml') (srel (Base.semi-MS x*))
    (semiMS-inj₁-coset x* ml')

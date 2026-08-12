------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization (arXiv:1310.6813, §6): a controlled-Z meeting two D
-- boxes.
--
-- altIZZDDIIDD, the M-side analogue of PushingZ's commZZIIBBBBI, and
-- the last of the five two-box families.
--
-- A controlled-Z at the very bottom of a staircase spans the pair of
-- D(0,1) and meets that box alone: altZZDD, which is local and lives in
-- Pushing.  One at (j,j+1) for j ≥ 1 is different -- it spans the pair
-- of D(j,j+1) while ALSO sharing wire j with D(j-1,j) -- so it meets
-- two boxes at once and needs these sixteen rules instead.
--
-- The paper writes the configuration ZZx 1 2, D ℓ₁ 0 1, D ℓ₂ 1 2: the
-- controlled-Z, then the LOWER box, then the upper one, which is the
-- order a staircase puts them in.  The arguments below follow that.
--
-- Two things to notice in the outputs.  The emitted controlled-Z is on
-- (0,1) -- one wire DOWN from the one that came in -- so it leaves below
-- both boxes and escapes rather than continuing up.  And what does
-- continue up is S gates on wire 2 and nothing else, so the ascending
-- part is a count here too, exactly as for the single-box families.
--
-- Rules 9 and 12 write their controlled-Z as ZZx 1 0 rather than
-- ZZx 0 1.  The gate is symmetric, so this is the same gate; it is
-- transcribed as ZZ₀₁ like the others.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.PushingD
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Product using (_×_ ; _,_)

open import ForStdlib.Data.Fin.Mod using (ℤ)
open import Notations using (₀ ; ₆ ; ₇)

open import Examples.Groups.Clifford.Qubit.Selinger.Boxes p-2 p-prime
open import Examples.Groups.Clifford.Qubit.Selinger.Pushing p-2 p-prime
  using (Dirty ; H₀ ; S₀ ; H₁ ; S₁ ; S₂ ; ZZ₀₁)

------------------------------------------------------------------------
-- The rules
--
-- Arguments are (lower , upper): the box on the controlled-Z's lower
-- pair first, as the paper writes them.

pushZZ-DD : DBox → DBox → ℤ 8 × (DBox × DBox) × List Dirty
pushZZ-DD d₁ d₁ = ₀ , (d₁ , d₁) , H₀ ∷ H₁ ∷ ZZ₀₁ ∷ H₀ ∷ H₁ ∷ []
pushZZ-DD d₁ d₂ = ₀ , (d₄ , d₂) , H₀ ∷ ZZ₀₁ ∷ H₀ ∷ []
pushZZ-DD d₁ d₃ = ₇ , (d₄ , d₃)
                , H₀ ∷ H₁ ∷ S₁ ∷ H₁ ∷ ZZ₀₁ ∷ H₀ ∷ S₁ ∷ H₁ ∷ S₁ ∷ []
pushZZ-DD d₁ d₄ = ₀ , (d₁ , d₄) , H₀ ∷ H₁ ∷ ZZ₀₁ ∷ H₀ ∷ H₁ ∷ []
pushZZ-DD d₂ d₁ = ₀ , (d₂ , d₄) , H₁ ∷ ZZ₀₁ ∷ H₁ ∷ []
pushZZ-DD d₂ d₂ = ₆ , (d₃ , d₃)
                , H₀ ∷ S₀ ∷ H₀ ∷ H₁ ∷ S₁ ∷ H₁ ∷ ZZ₀₁ ∷ S₀ ∷ S₁ ∷ []
pushZZ-DD d₂ d₃ = ₇ , (d₃ , d₂)
                , H₀ ∷ S₀ ∷ H₀ ∷ ZZ₀₁ ∷ S₀ ∷ H₁ ∷ S₁ ∷ S₂ ∷ S₂ ∷ []
pushZZ-DD d₂ d₄ = ₀ , (d₂ , d₁) , H₁ ∷ ZZ₀₁ ∷ H₁ ∷ []
pushZZ-DD d₃ d₁ = ₇ , (d₃ , d₄)
                , H₁ ∷ H₀ ∷ S₀ ∷ H₀ ∷ ZZ₀₁ ∷ S₀ ∷ H₀ ∷ S₀ ∷ H₁ ∷ []
pushZZ-DD d₃ d₂ = ₇ , (d₂ , d₃)
                , H₁ ∷ S₁ ∷ H₁ ∷ ZZ₀₁ ∷ H₀ ∷ S₀ ∷ S₁ ∷ S₂ ∷ S₂ ∷ []
pushZZ-DD d₃ d₃ = ₀ , (d₂ , d₂) , ZZ₀₁ ∷ H₀ ∷ S₀ ∷ H₁ ∷ S₁ ∷ []
pushZZ-DD d₃ d₄ = ₇ , (d₃ , d₁)
                , H₁ ∷ H₀ ∷ S₀ ∷ H₀ ∷ ZZ₀₁ ∷ S₀ ∷ H₀ ∷ S₀ ∷ H₁ ∷ []
pushZZ-DD d₄ d₁ = ₀ , (d₄ , d₁) , H₀ ∷ H₁ ∷ ZZ₀₁ ∷ H₀ ∷ H₁ ∷ []
pushZZ-DD d₄ d₂ = ₀ , (d₁ , d₂) , H₀ ∷ ZZ₀₁ ∷ H₀ ∷ []
pushZZ-DD d₄ d₃ = ₇ , (d₁ , d₃)
                , H₀ ∷ H₁ ∷ S₁ ∷ H₁ ∷ ZZ₀₁ ∷ H₀ ∷ S₁ ∷ H₁ ∷ S₁ ∷ []
pushZZ-DD d₄ d₄ = ₀ , (d₄ , d₄) , H₀ ∷ H₁ ∷ ZZ₀₁ ∷ H₀ ∷ H₁ ∷ []

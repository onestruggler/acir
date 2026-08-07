{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --termination-depth=20 #-}

------------------------------------------------------------------------
-- Qudit Clifford group mod scalars.
--
-- This module is an aggregator: the development is split across the
-- files in the `Clifford-Mod-Scalar/` folder, by subject.  It
-- re-exports all of them publicly, so every existing importer
-- (`open import Examples.Groups.Clifford.Qupit.Simplified-V1.Clifford-Mod-Scalar …`) sees exactly the same
-- names as before the split:
--
--   Syntactics : shared preamble (patterns, 𝑠/1/2, Symplectic), the
--                relation Clifford-Relations, and its structural
--                lemmas Lemmas-Clifford
--   Lemmas     : Lemmas1 (the M-lemmas: M-mul, M-power, order-M, …)
--                and Clifford-GroupLike
--   Tactics    : the word tactics — CommData-Sim,
--                Commuting-Symplectic-Sim, Rewriting-Sim, Sim-Rewriting
--   LemmasXZ   : Lemmas1b, the X/Z-conjugation lemmas (lemma-HH-X,
--                lemma-SX, lemma-HSH, …), which use the rewriting
--                tactic and so come after it
--
-- The dependency order is exactly that: each file imports the ones
-- above it.  Only Syntactics is re-exported in full; the others export
-- their own modules, since their preambles are copies of Syntactics'
-- and taking them again would be a duplicate definition.
--
-- The previous abandoned WIP tail (incomplete proofs with `{!!}` holes,
-- formerly block-commented) lives in archive/Clifford-Mod-Scalar-tail.agda.txt
-- and is not part of the build.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (_,_ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Nat.Primality
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem
open import Notations

module Examples.Groups.Clifford.Qupit.Simplified-V1.Clifford-Mod-Scalar
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

-- Syntactics carries the shared preamble (patterns, 1/2, Symplectic, …)
-- and the first modules; re-export it in full.  From the others
-- re-export only their own modules.
open import Examples.Groups.Clifford.Qupit.Simplified-V1.Clifford-Mod-Scalar.Syntactics p-3 p-prime g* g-gen public
open import Examples.Groups.Clifford.Qupit.Simplified-V1.Clifford-Mod-Scalar.Lemmas p-3 p-prime g* g-gen public
  using (module Lemmas1 ; module Clifford-GroupLike)
open import Examples.Groups.Clifford.Qupit.Simplified-V1.Clifford-Mod-Scalar.Tactics p-3 p-prime g* g-gen public
  using ( module CommData-Sim ; module Commuting-Symplectic-Sim
        ; module Rewriting-Sim ; module Sim-Rewriting )
open import Examples.Groups.Clifford.Qupit.Simplified-V1.Clifford-Mod-Scalar.LemmasXZ p-3 p-prime g* g-gen public
  using (module Lemmas1b)

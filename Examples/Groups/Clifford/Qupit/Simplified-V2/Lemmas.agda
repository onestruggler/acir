{-# OPTIONS --cubical-compatible --termination-depth=20 #-}
{-# OPTIONS --inversion-max-depth=1000 #-}

------------------------------------------------------------------------
-- Re-derivation of the Clifford conjugation base-lemma subtree for the
-- *Simplified* presentation (route (B): fully machine-checked).
--
-- This module is an aggregator: the development is split across the
-- files in the `Lemmas/` folder, by subject.  It re-exports all of them
-- publicly, so importers see one flat set of names:
--
--   Base         : Lemmas1-S — the base lemmas (M-mul, the orders of
--                  H, X and Z, the S/H commutations)
--   Structural   : Lemmas-Clifford-S (cong↑ and friends),
--                  Simplified-GroupLike-S, and Lemmas1b-S
--   Conjugation  : the standalone 𝑠/Z/CZ conjugation lemmas, with the
--                  CL / CLb glue onto Base and Structural
--   Completeness : the tail-c10/c11 cascade, C10, C11, Completeness-S
--
-- Each file imports its predecessor with `public`, so re-exporting
-- Completeness alone transitively re-exports the whole subtree.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (_,_ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Nat.Primality
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem
open import Notations

module Examples.Groups.Clifford.Qupit.Simplified-V2.Lemmas
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Examples.Groups.Clifford.Qupit.Simplified-V2.Lemmas.Completeness
  p-3 p-prime g* g-gen public

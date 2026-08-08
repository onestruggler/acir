------------------------------------------------------------------------
-- Presentations of groups
--
-- The symplectic presentation, with surjectivity discharged
--
-- Presentation.agda proves soundness and completeness outright and
-- leaves surjectivity as a hypothesis, which is what keeps it --safe.
-- This module discharges that hypothesis with Surjectivity.surj-nf and
-- so states the presentation theorem in full.
--
-- Surjectivity is proved, not postulated: Surjectivity.agda and
-- TheoremLM.agda long carried comments saying Theorem-LM was an open
-- input, but neither file contains a postulate — the only one in the
-- library is in ExtendedGate.NF-Inj-Base, which is not in this cone.
-- They merely lacked --safe.  So this module, and hence the whole
-- presentation theorem, is postulate-free.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.PresentationFull
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Sp-group)
open import Examples.Groups.Symplectic.Presentation p-2 p-prime
  using (presentation-from)
open import Examples.Groups.Symplectic.Surjectivity p-2 p-prime
  using (surj-nf)

------------------------------------------------------------------------
-- The presentation theorem

presentation : ∀ {n} → (n QRel,_===_) IsPresentationOf (Sp-group n)
presentation {n} = presentation-from {n} surj-nf

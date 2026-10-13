------------------------------------------------------------------------
-- Entry point for the checked circuit transcription and matrix theory.
-- This does not assert completeness of the circuit relation set.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Theorems where

open import Examples.Groups.CCX+HH-3qubit.Syntactics public
open import Examples.Groups.CCX+HH-3qubit.Interpretation public
open import Examples.Groups.CCX+HH-3qubit.Soundness public
open import Examples.Groups.CCX+HH-3qubit.GroupLike public using (grouplike)
open import Examples.Groups.CCX+HH-3qubit.Normalization public
  using (Normal ; normalize ; past-gen ; past-word)
import Examples.Groups.CCX+HH-3qubit.Errata as Errata
import Examples.Groups.CCX+HH-3qubit.Semantics as Semantics

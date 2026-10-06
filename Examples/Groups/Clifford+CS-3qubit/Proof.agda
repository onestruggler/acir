------------------------------------------------------------------------
-- Presentations of groups
--
-- This module collects the proofs of the soundness and completeness
-- theorems, which were proved separately in Soundness.agda and
-- Completeness.agda, into a single file for easy checking.
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


open import Examples.Groups.Clifford+CS-3qubit.Theorem
import Examples.Groups.Clifford+CS-3qubit.Completeness as Completeness
import Examples.Groups.Clifford+CS-3qubit.Soundness as Soundness

module Examples.Groups.Clifford+CS-3qubit.Proof where

  soundness : soundness-property
  soundness = Soundness.soundness


  completeness : completeness-property
  completeness = Completeness.completeness

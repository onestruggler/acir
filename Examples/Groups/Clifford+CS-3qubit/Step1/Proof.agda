------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS-3qubit.Step1.Theorem using (completeness-property ; soundness-property)
import Examples.Groups.Clifford+CS-3qubit.Step1.Completeness as Completeness
import Examples.Groups.Clifford+CS-3qubit.Step1.Soundness as Soundness

module Examples.Groups.Clifford+CS-3qubit.Step1.Proof where

  soundness : soundness-property
  soundness = Soundness.soundness

  completeness : completeness-property
  completeness = Completeness.completeness

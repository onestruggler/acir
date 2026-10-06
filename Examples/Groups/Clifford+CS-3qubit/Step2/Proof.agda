------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS-3qubit.Step2.Theorem using (completeness-property ; soundness-property)
import Examples.Groups.Clifford+CS-3qubit.Step2.Soundness as Soundness

module Examples.Groups.Clifford+CS-3qubit.Step2.Proof where

  soundness : soundness-property
  soundness = Soundness.soundness

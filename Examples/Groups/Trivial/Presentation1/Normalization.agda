------------------------------------------------------------------------
-- Presentations of groups
--
-- The normal form for ⟨ ⊥ ∣ ⟩.
--
-- Nothing is proved here: the generic collapse argument of
-- Examples.Groups.Trivial.Normalization is instantiated at this
-- presentation's gen≈ε, and its results are re-exported unchanged.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Presentation1.Normalization where

open import Examples.Groups.Trivial.Presentation1.Syntactics
  using (pres ; gen≈ε)

import Examples.Groups.Trivial.Normalization as Generic

------------------------------------------------------------------------
-- w≈ε, nf, nfp, nfp'

open Generic pres gen≈ε public

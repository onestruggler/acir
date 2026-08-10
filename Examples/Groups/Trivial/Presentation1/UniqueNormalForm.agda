------------------------------------------------------------------------
-- Presentations of groups
--
-- Uniqueness of the normal form for ⟨ ⊥ ∣ ⟩.
--
-- The generic argument of Examples.Groups.Trivial.UniqueNormalForm,
-- instantiated at this presentation's gen≈ε.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Presentation1.UniqueNormalForm where

open import Examples.Groups.Trivial.Presentation1.Syntactics
  using (pres ; gen≈ε)

import Examples.Groups.Trivial.UniqueNormalForm as Generic

------------------------------------------------------------------------
-- unfp

open Generic pres gen≈ε public

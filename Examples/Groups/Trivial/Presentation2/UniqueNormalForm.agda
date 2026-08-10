------------------------------------------------------------------------
-- Presentations of groups
--
-- Uniqueness of the normal form for ⟨ A ∣ w = ε for every word w ⟩.
--
-- The generic argument of Examples.Groups.Trivial.UniqueNormalForm,
-- instantiated at this presentation's gen≈ε.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Presentation2.UniqueNormalForm (A : Set) where

open import Examples.Groups.Trivial.Presentation2.Syntactics A
  using (pres ; gen≈ε)

import Examples.Groups.Trivial.UniqueNormalForm as Generic

------------------------------------------------------------------------
-- unfp

open Generic pres gen≈ε public

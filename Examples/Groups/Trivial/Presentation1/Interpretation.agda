------------------------------------------------------------------------
-- Presentations of groups
--
-- The interpretation of ⟨ ⊥ ∣ ⟩ in the terminal group.
--
-- As with Normalization, this only instantiates the generic argument of
-- Examples.Groups.Trivial.Interpretation at this presentation's gen≈ε.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Presentation1.Interpretation where

open import Examples.Groups.Trivial.Presentation1.Syntactics
  using (pres ; gen≈ε)

import Examples.Groups.Trivial.Interpretation as Generic

------------------------------------------------------------------------
-- ⟦_⟧₀, GS, fʷ-cong-ax, grouplike

open Generic pres gen≈ε public

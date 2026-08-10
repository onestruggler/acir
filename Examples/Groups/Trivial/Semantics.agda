------------------------------------------------------------------------
-- Presentations of groups
--
-- Semantics of the trivial group: the terminal group, whose carrier is
-- ⊤ and whose equality relates every pair of elements.
--
-- Both presentations target this same group, so it is stated once here
-- and shared by Presentation and Presentation-Alt.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Semantics where

open import Algebra.Bundles using (Group)
open import Level using (0ℓ)

import Algebra.Construct.Terminal as Terminal

------------------------------------------------------------------------
-- The target group

gp : Group 0ℓ 0ℓ
gp = Terminal.group

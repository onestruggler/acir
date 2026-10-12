------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 4 is complete for real-Clifford+CH circuits (Clément,
-- Theorem 8.9), unconditionally
--
-- CompletenessInduction proves Theorem 8.9 at every width from the one
-- theorem the paper imports, Theorem 4.4: completeness of Figure 6 for
-- the proper words over the one- and two-level generators.  That
-- theorem is proved in Auxiliary.Theorem44Proof, from the presentation
-- of O_N(ℤ[1/√2]) by Figure 6 in Real-Clifford+CH-TwoLevel-Clement.
-- So two circuits with the same matrix over ℤ[1/√2] are equal by
-- Figure 4 and the swap rules, at every width (completeness), and the
-- rules present the monoid of those matrices (subpresentation).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH.Presentation where

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem44Proof using (theorem-4-4₂ ; theorem-4-4ₙ)
open import Examples.Groups.Real-Clifford+CH.CompletenessInduction using (module Theorem-8-9-from-4-4)

open Theorem-8-9-from-4-4 theorem-4-4₂ theorem-4-4ₙ public using (completeness ; subpresentation)

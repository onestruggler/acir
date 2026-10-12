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
--
-- Read in the orthogonal group O_{2ⁿ}(ℤ[1/√2]) of Real-Clifford+CH-
-- TwoLevel instead, the group Hadamard-Pi's Figure 6 presents, the same
-- theorem is a group sub-presentation (subpresentationᴼ, from
-- Orthogonal): the rules present the subgroup the circuits on n wires
-- generate.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH.Presentation where

open import Data.Nat.Base using (ℕ ; _^_)

open import Presentation.Definitions using (_IsSubPresentationOf_)

open import Examples.Groups.Real-Clifford+CH.Syntactics using (_VRel,_===_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem44Proof using (theorem-4-4₂ ; theorem-4-4ₙ)
open import Examples.Groups.Real-Clifford+CH.CompletenessInduction using (module Theorem-8-9-from-4-4)
import Examples.Groups.Real-Clifford+CH.Orthogonal as Orthogonal
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (O)

open Theorem-8-9-from-4-4 theorem-4-4₂ theorem-4-4ₙ public using (completeness ; subpresentation)

-- Figure 4 presents the subgroup of O_{2ⁿ}(ℤ[1/√2]) that the circuits
-- on n wires generate.
subpresentationᴼ : ∀ n → (n VRel,_===_) IsSubPresentationOf O (2 ^ n)
subpresentationᴼ n = Orthogonal.subpresentationᴼ completeness {n}

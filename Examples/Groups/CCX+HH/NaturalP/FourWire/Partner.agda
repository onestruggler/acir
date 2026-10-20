------------------------------------------------------------------------
-- Presentations of groups
--
-- The subgroup P₀ of four-wire circuits that use wire 0 only through
-- HH gates is the image of the three-wire CCX+H group under the
-- Hadamard embedding ψ.  Given R4, the CCX+HH rules are complete on it:
-- two CCX+H circuits on three wires with the same matrix have images
-- that the CCX+HH rules on four wires relate.  This is CCX+H's
-- completeness on three wires (ThreeWire.Complete), carried by
-- Transport.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.CCX+HH.NaturalP.FourWire.Embed using (R4)

module Examples.Groups.CCX+HH.NaturalP.FourWire.Partner (r4 : R4) where

open import Relation.Binary.PropositionalEquality using (_≡_)

import Examples.Groups.CCX+H.NaturalP.Schema as H
import Examples.Groups.CCX+HH.NaturalP.Schema as S
open import Examples.Groups.CCX+H.NaturalP.Soundness using (interpretH)
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Complete using (complete₃)
open import Examples.Groups.CCX+HH.NaturalP.FourWire.Embed using (ψ)
open import Examples.Groups.CCX+HH.NaturalP.FourWire.Transport r4 using (transport)

partner-complete : ∀ {u v : H.Circuit 3} →
                   interpretH u ≡ interpretH v → 4 S.⊢ ψ u ≈ ψ v
partner-complete {u} {v} p = transport {u} {v} (complete₃ {u} {v} p)

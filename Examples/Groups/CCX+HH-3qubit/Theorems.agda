------------------------------------------------------------------------
-- Presentations of groups
--
-- The corrected paper rules are sound and admit H₂ normal forms.
-- With the retained controlled-K definition, they are also complete
-- and present the exact scaled dyadic orthogonal group L₈.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Theorems where

open import Examples.Groups.CCX+HH-3qubit.Syntactics public
open import Examples.Groups.CCX+HH-3qubit.Interpretation public
open import Examples.Groups.CCX+HH-3qubit.Soundness public
open import Examples.Groups.CCX+HH-3qubit.GroupLike public using (grouplike)
open import Examples.Groups.CCX+HH-3qubit.Normalization public
  using (Normal ; normalize ; past-gen ; past-word)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Presentation public
  using (ToffoliHadamard)
open import Presentation.Definitions using (_IsPresentationOf_)
import Examples.Groups.CCX+HH-3qubit.Repaired.Presentation as P
import Examples.Groups.CCX+HH-3qubit.Repaired.Soundness as RS
import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics as Repaired
import Examples.Groups.CCX+HH-3qubit.Errata as Errata
import Examples.Groups.CCX+HH-3qubit.Semantics as Semantics

-- The relation in these results includes K-definition. The
-- soundness and normalization results above use the paper rules alone.
repaired-soundness : ∀ {w v} → Repaired._≈_ w v →
                     ⟦ w ⟧ ~ ⟦ v ⟧
repaired-soundness {w} {v} = RS.sound {w} {v}

repaired-completeness : ∀ {w v} → ⟦ w ⟧ ~ ⟦ v ⟧ →
                        Repaired._≈_ w v
repaired-completeness {w} {v} = P.completeness {w} {v}

repaired-presentation : Repaired._===_ IsPresentationOf ToffoliHadamard
repaired-presentation = P.presentation

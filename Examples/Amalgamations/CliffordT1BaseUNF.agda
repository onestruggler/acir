------------------------------------------------------------------------
-- Presentations of groups
--
-- Uniqueness of the Clifford+T base normal form: the ⟨ω⟩ × ⟨S⟩ level
-- of Examples.Amalgamations.CliffordT1 (carrier Fin 8 × Fin 4) is
-- unique for the direct-product semantics ℤ/8ℤ × ℤ/4ℤ, lifted from
-- the two cyclic unique-normal-form witnesses through the
-- direct-product construction.  This lives in its own module because
-- the cyclic semantics does not carry the --cubical-compatible flag
-- that Examples.Amalgamations.CliffordT1 does.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Amalgamations.CliffordT1BaseUNF where

open import Algebra.Bundles using (Group)
open import Data.Product using (_×_)
import Relation.Binary.PropositionalEquality as Eq

import Normalization.NormalForm.Setoid as SNF
open import Presentation.Construct.Base using (_⊕_)
import Presentation.Construct.Properties.DirectProduct as DP

import Examples.Groups.Cyclic.Normalization as Cyclic
import Examples.Groups.Cyclic.Semantics as CycSem
import Examples.Groups.Cyclic.Theorems as CycThm
open import Examples.Amalgamations.CliffordT1 using (module Sω)

private
  module DNF   = DP Sω.Pω Sω.PS
  module DPres = DNF.Presentation (CycSem.Cn-group 8) (CycSem.Cn-group 4)
                   CycThm.presentation CycThm.presentation

-- ℤ/8ℤ × ℤ/4ℤ, the direct-product semantics of the base.
Z8×Z4 : Group _ _
Z8×Z4 = DPres.dp

-- The interpretation of base words in ℤ/8ℤ × ℤ/4ℤ.
⟦_⟧ = DPres.⟦_⟧

unfp' : SNF.UniqueNormalForm (Sω.Pω ⊕ Sω.PS)
          (Eq.setoid (Cyclic.NF 8 × Cyclic.NF 4))
          (Group.setoid Z8×Z4) DPres.⟦_⟧ Sω.nfp'
unfp' = DPres.LiftUNF.unfp' (Cyclic.nfp' 8) (Cyclic.nfp' 4)
          (CycThm.unique-nf 8) (CycThm.unique-nf 4)

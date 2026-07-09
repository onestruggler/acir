------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ and their normal form via coset enumeration
-- Adapted to the Circuit / Lift-Relation framework
------------------------------------------------------------------------

{-# OPTIONS  --safe #-}

module Examples.Construct.DirectProduct.S3xC5.Semantic where

open import Data.Product using (_,_)

open import Word.Base using (Word)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Fin using (Fin)
open import Notations

open import Examples.Groups.Symmetric.Syntactics using (_VRel,_===_)
open import Examples.Groups.Cyclic.Normalization using (_Cn,_===_)
import Examples.Groups.Cyclic.Semantics as CS
import Examples.Groups.Symmetric.Tight.Semantics as TS

open import Examples.Construct.DirectProduct.S3xC5.Syntactics
open import Algebra.Bundles using (Group)
import Algebra.Construct.DirectProduct as ADP


-- Direct product of the permutation group S₃ and the cyclic group C₅.
S₃×C₅-group : Group _ _
S₃×C₅-group = ADP.group (TS.Permutation′-group 3) (CS.Cn-group 5)


open import Function.Construct.Identity using (↔-id)

⟦_⟧₀ : Y → Group.Carrier S₃×C₅-group
⟦ inj₁ x  ⟧₀ = TS.⟦ x  ⟧ᵍ , ₀
⟦ inj₂ y  ⟧₀ = ↔-id (Fin 3) , CS.⟦_⟧₀ {5} y


⟦_⟧ : Word Y → Group.Carrier S₃×C₅-group
⟦_⟧ = E.⟦_⟧
  where
  open import Normalization.StarInterp (_===_)
  module E = Extend (Group.monoid S₃×C₅-group) ⟦_⟧₀

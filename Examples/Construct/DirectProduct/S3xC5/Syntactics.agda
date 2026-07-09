------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ and their normal form via coset enumeration
-- Adapted to the Circuit / Lift-Relation framework
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Construct.DirectProduct.S3xC5.Syntactics where

open import Notations

open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Cyclic.Normalization

open import Presentation.Construct.Base

open import Presentation.Construct.Properties.DirectProduct (₃ VRel,_===_) (5 Cn,_===_) using (Y ; module NFP') public

infix 4 _===_
_===_ = ((₃ VRel,_===_) ⋄ (5 Cn,_===_) ⋄ CommRel)

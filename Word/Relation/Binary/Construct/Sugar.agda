------------------------------------------------------------------------
-- Presentations of groups
--
-- The sugar relation: each newly added generator m is definable as a
-- word f m over the base alphabet, and desugars to it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Word.Relation.Binary.Construct.Sugar where

open import Data.Sum using (_⊎_ ; inj₁)

open import Word.Base
open import Word.Relation.Binary.Construct.Base using ([_]ᵣ)

-- Sugar relation.  Each newly added generator m desugars to a word
-- over A.
data SugarRel {M A} (f : M → Word A) : WRel (M ⊎ A) where
  desugar : ∀ {m} → SugarRel f [ inj₁ m ]ʷ [ f m ]ᵣ

------------------------------------------------------------------------
-- Presentations of groups
--
-- The universal (coarsest) relation, identifying every word with ε.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Word.Relation.Binary.Construct.Trivial where

open import Word.Base

-- The coarsest relation: every word is identified with ε.
data TrivialRel {A} : WRel A where
  ≈ε : ∀ {w} → TrivialRel {A} w ε

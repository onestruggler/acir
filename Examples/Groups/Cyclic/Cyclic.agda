------------------------------------------------------------------------
-- Presentations of groups
--
-- Aggregator for the cyclic group ℤ/Nℤ: re-exports the syntactics
-- (generator, relation, pres) together with the normal form (nfp,
-- nfp', NF) under a single module name for convenient qualified use.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Cyclic.Cyclic where

open import Examples.Groups.Cyclic.Normalization public

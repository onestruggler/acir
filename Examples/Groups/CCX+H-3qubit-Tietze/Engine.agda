------------------------------------------------------------------------
-- Replay a concrete rewrite, retaining the surrounding word.
-- All generated certificates reduce to the repository's congruence
-- constructors; the search programs are outside the trusted proof.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Engine where

open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Presentation.Base _===_ public hiding (_===_ ; _≈_)
open import Presentation.Properties _===_ public using (by-assoc ; by-assoc-and)
open import Relation.Binary.PropositionalEquality as Eq public using ()

under : ∀ {a b} (prefix suffix : Word Gen) → a ≈ b →
        prefix • a • suffix ≈ prefix • b • suffix
under prefix suffix e = cong refl (cong e refl)

------------------------------------------------------------------------
-- Presentations of groups
--
-- X on the box wire of the four-wire H gate H● of the proof of (353)
-- passes it, decided (for the proof of (355), GeneralN.Canon23)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base355 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base353 using (H●)

e-X₃● : Evaluated {4} (X ↑ ↑ ↑ • H● • X ↑ ↑ ↑) H●
e-X₃● = evaluated Eq.refl

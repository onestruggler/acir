------------------------------------------------------------------------
-- Presentations of groups
--
-- (322) and (323) on four wires, decided (Clément, Lemma D.12)
--
-- The triply controlled ZX on wire 0 between P ⊗ P on the wires 0 1,
-- with its control on wire 3 of either colour (`Aᴾ α true true` of
-- FourQubit.PForms, spelled here without its parameterised modules),
-- commutes with the doubly controlled box with wire 3 idle, white on
-- wire 2, its box wire on wire 0 or on wire 1 (`d322`): the base of
-- GeneralN.Gadget322's induction, which the paper takes from (247) and
-- (248).  Each an evaluation of a few seconds; in a module of its own,
-- since Agda frees the memory of an evaluation only when its module is
-- done.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base322 where

open import Data.Bool using (Bool ; true ; false)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; Vb)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place)

-- X on wire 3 around w when α is false.
N3F : Bool → Circuit 4 → Circuit 4
N3F true  w = w
N3F false w = X ↑ ↑ ↑ • w • X ↑ ↑ ↑

-- FourQubit.PForms' Aᴾ α true true on four wires.
AᴾF : Bool → Circuit 4
AᴾF α = PP ↓ • N3F α (ΛZX 3 ↓ᵏ 0) • PP ↓

-- The placed box.
P322 : Bool → Circuit 4
P322 v = place 3 (col (true ∷ true ∷ false ∷ []) (Vb v 0))

d322 : ∀ (α v : Bool) → Evaluated (AᴾF α • P322 v) (P322 v • AᴾF α)
d322 true  true  = evaluated Eq.refl
d322 true  false = evaluated Eq.refl
d322 false true  = evaluated Eq.refl
d322 false false = evaluated Eq.refl

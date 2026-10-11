------------------------------------------------------------------------
-- Presentations of groups
--
-- (322) and (323) on four wires, decided (Clément, Lemma D.12)
--
-- The triply controlled ZX on wire 0 between P ⊗ P on the wires 0 1,
-- with its controls on the wires 1 and 3 of either colour
-- (`Aᴾ α β true` of FourQubit.PForms, spelled here without its
-- parameterised modules), commutes with the doubly controlled box with
-- wire 3 idle, white on wire 2, its box wire on wire 0 or on wire 1 and
-- its control on the other of those two of either colour (`d322`): the
-- base of GeneralN.Gadget322's induction, which the paper takes from
-- (247) and (248).  Here the cases with the control on wire 1 black;
-- Base322b has those with it white.  Each an evaluation of a few
-- seconds; in modules of their own, since Agda frees the memory of an
-- evaluation only when its module is done.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base322 where

open import Data.Bool using (Bool ; true ; false)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; Vb ; bot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place)

-- X on wire 3, resp. wire 1, around w when the colour is false.
N3F N1F : Bool → Circuit 4 → Circuit 4
N3F true  w = w
N3F false w = X ↑ ↑ ↑ • w • X ↑ ↑ ↑
N1F true  w = w
N1F false w = X ↑ • w • X ↑

-- FourQubit.PForms' Aᴾ α β true on four wires.
AᴾF : Bool → Bool → Circuit 4
AᴾF α β = PP ↓ • N3F α (N1F β (ΛZX 3 ↓ᵏ 0)) • PP ↓

-- The placed box.
P322 : Bool → Bool → Circuit 4
P322 v γ = place 3 (col (bot v γ []) (Vb v 0))

d322 : ∀ (α γ v : Bool) → Evaluated (AᴾF α true • P322 v γ) (P322 v γ • AᴾF α true)
d322 true  true  true  = evaluated Eq.refl
d322 true  true  false = evaluated Eq.refl
d322 true  false true  = evaluated Eq.refl
d322 true  false false = evaluated Eq.refl
d322 false true  true  = evaluated Eq.refl
d322 false true  false = evaluated Eq.refl
d322 false false true  = evaluated Eq.refl
d322 false false false = evaluated Eq.refl

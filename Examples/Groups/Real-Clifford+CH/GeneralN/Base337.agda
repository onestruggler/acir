------------------------------------------------------------------------
-- Presentations of groups
--
-- The rotation pairs of (337), decided (Clément, Lemma D.13)
--
-- `d337r b c`: the triply controlled ZX of the box's (320), on wire 0
-- (b true) or on wire 1 (b false), against the triply controlled ZX of
-- the H gate's, on wire 0 (c true) or on wire 1 (c false), between P ⊗ P
-- on the wires 0 1 and white on wire 2 — the rotation pairs of
-- GeneralN.Box337 on the bottom four wires.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base337 where

open import Data.Bool using (Bool ; true ; false)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)

-- The triply controlled ZX on wire 0 (true) or on wire 1 (false).
U₄ : Bool → Circuit 4
U₄ true  = ΛZX 3
U₄ false = Ex ↓ • ΛZX 3 • Ex ↓

-- The H gate's, between P ⊗ P on the wires 0 1 and white on wire 2.
G2 : Bool → Circuit 4
G2 c = X ↑ ↑ • (PP ↓ • U₄ c • PP ↓) • X ↑ ↑

d337r : ∀ (b c : Bool) → Evaluated (U₄ b • G2 c) (G2 c • U₄ b)
d337r true  true  = evaluated Eq.refl
d337r true  false = evaluated Eq.refl
d337r false true  = evaluated Eq.refl
d337r false false = evaluated Eq.refl

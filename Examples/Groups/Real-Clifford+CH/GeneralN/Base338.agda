------------------------------------------------------------------------
-- Presentations of groups
--
-- (338) and (320) on four wires, decided (Clément, Lemma D.13)
--
-- The box Λ□ 3 commutes with the H gate on wire 0 whose box wire is
-- wire 1, in each colouring of the H gate's controls on the wires 2 3
-- (`d338`); and the box is the product (320) of the triply controlled
-- rotations and the doubly controlled box with wire 3 idle, also on
-- four wires (`d320`), where (320) proper (GeneralN.Box320) starts at
-- five.  Each an evaluation of a few seconds: with completeness on four
-- wires, an equation (GeneralN.Gadget322, GeneralN.Box338).  In a module
-- of their own: Agda frees the memory of an evaluation only when its
-- module is done.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base338 where

open import Data.Bool using (Bool ; true ; false)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; Hg)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place)

d338 : ∀ (b c : Bool) →
       Evaluated (Λ□ 3 • col (true ∷ true ∷ b ∷ c ∷ []) (Hg 1)) (col (true ∷ true ∷ b ∷ c ∷ []) (Hg 1) • Λ□ 3)
d338 true  true  = evaluated Eq.refl
d338 true  false = evaluated Eq.refl
d338 false true  = evaluated Eq.refl
d338 false false = evaluated Eq.refl

-- (320) on four wires, spelled as GeneralN.Gadget322's product of
-- letters at width 4 + 0.
W320 : Circuit 4
W320 = (ΛZX 3 ↓ᵏ 0) • (Ex ↓ • (ΛZX 3 ↓ᵏ 0) • Ex ↓) • place 3 (Λ□ 2) • (Ex ↓ • (ΛXZ 3 ↓ᵏ 0) • Ex ↓) •
       (ΛXZ 3 ↓ᵏ 0) • (Ex ↓ • (ΛZX 3 ↓ᵏ 0) • Ex ↓) • place 3 (Λ□ 2) • (Ex ↓ • (ΛXZ 3 ↓ᵏ 0) • Ex ↓) • ε

d320 : Evaluated (Λ□ 3) W320
d320 = evaluated Eq.refl

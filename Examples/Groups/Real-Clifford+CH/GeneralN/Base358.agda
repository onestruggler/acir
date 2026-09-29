------------------------------------------------------------------------
-- Presentations of groups
--
-- Two-wire facts for (358), decided
--
-- The rotations on two wires, ΛXZ 1 and ΛZX 1 (target wire 0, control
-- wire 1), are inverse, and ΛXZ 1 • (Ex • ΛZX 1 • Ex) • ΛXZ 1 is CZ • Ex:
-- the controlled rotations merged over every colouring of the wires
-- 2 … in GeneralN.Canon358.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base358 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)

e-ebe : Evaluated {2} (ΛXZ 1 • (Ex • ΛZX 1 • Ex) • ΛXZ 1) (CZ • Ex)
e-ebe = evaluated Eq.refl

e-zxxz : Evaluated {2} (ΛZX 1 • ΛXZ 1) ε
e-zxxz = evaluated Eq.refl

e-xzzx : Evaluated {2} (ΛXZ 1 • ΛZX 1) ε
e-xzzx = evaluated Eq.refl

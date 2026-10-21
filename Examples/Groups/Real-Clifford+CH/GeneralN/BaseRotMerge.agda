------------------------------------------------------------------------
-- Presentations of groups
--
-- (354) on the top wire at two and three wires, decided
--
-- A white and a black control of the rotation on wire 0 merge on the
-- top wire into the rotation of one control fewer placed around it,
-- (Xat j • ΛZX j • Xat j) • ΛZX j ≈ placeAt j (ΛZX (j − 1)), and the
-- same for ΛXZ: the widths below five of the merge over every
-- colouring in GeneralN.RotMerge.  On four wires they are Base4's
-- `e-zx3`, `e-xz3`, which share its reading of the rotations.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.BaseRotMerge where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)

e-zx1 : Evaluated {2} ((Xat 1 • ΛZX 1 • Xat 1) • ΛZX 1) (placeAt 1 (ΛZX 0))
e-zx1 = evaluated Eq.refl

e-zx2 : Evaluated {3} ((Xat 2 • ΛZX 2 • Xat 2) • ΛZX 2) (placeAt 2 (ΛZX 1))
e-zx2 = evaluated Eq.refl

e-xz1 : Evaluated {2} ((Xat 1 • ΛXZ 1 • Xat 1) • ΛXZ 1) (placeAt 1 (ΛXZ 0))
e-xz1 = evaluated Eq.refl

e-xz2 : Evaluated {3} ((Xat 2 • ΛXZ 2 • Xat 2) • ΛXZ 2) (placeAt 2 (ΛXZ 1))
e-xz2 = evaluated Eq.refl

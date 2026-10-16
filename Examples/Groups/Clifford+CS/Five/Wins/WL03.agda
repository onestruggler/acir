------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL03 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl0463 : Complete 4 → ⟪ (CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) ⟫ʷ
wl0463 c4 = lw0 c4 (CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) tt tt Eq.refl

wl0464 : Complete 4 → ⟪ (CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) ⟫ʷ
wl0464 c4 = lw4 c4 (CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) tt tt Eq.refl

wl0465 : Complete 4 → ⟪ (CCZ123 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14⁻ ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
wl0465 c4 = lw0 c4 (CCZ123 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0466 : Complete 4 → ⟪ (CCZ123 ∷ X1 ∷ S1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S1 ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
wl0466 c4 = lw4 c4 (CCZ123 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0467 : Complete 4 → ⟪ (CK10⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CK10⁻ ∷ []) ⟫ʷ
wl0467 c4 = lw4 c4 (CK10⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CK10⁻ ∷ []) tt tt Eq.refl

wl0468 : Complete 4 → ⟪ (CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S1 ∷ X1 ∷ CK10⁻ ∷ []) ⟫ʷ
wl0468 c4 = lw4 c4 (CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CK10⁻ ∷ []) tt tt Eq.refl

wl0469 : Complete 4 → ⟪ (CS14 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14⁻ ∷ X1 ∷ CS14 ∷ []) ⟫ʷ
wl0469 c4 = lw0 c4 (CS14 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS14 ∷ []) tt tt Eq.refl

wl0470 : Complete 4 → ⟪ (CS14 ∷ X1 ∷ S1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S1 ∷ X1 ∷ CS14 ∷ []) ⟫ʷ
wl0470 c4 = lw0 c4 (CS14 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS14 ∷ []) tt tt Eq.refl

wl0471 : Complete 4 → ⟪ (S1⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ S1⁻ ∷ []) ⟫ʷ
wl0471 c4 = lw4 c4 (S1⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl

wl0472 : Complete 4 → ⟪ (S1⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14⁻ ∷ X1 ∷ S1⁻ ∷ []) ⟫ʷ
wl0472 c4 = lw0 c4 (S1⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl

wl0473 : Complete 4 → ⟪ (S1⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S1 ∷ X1 ∷ S1⁻ ∷ []) ⟫ʷ
wl0473 c4 = lw4 c4 (S1⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl

wl0474 : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0474 c4 = lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl

wl0475 : Complete 4 → ⟪ (CK10 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0475 c4 = lw4 c4 (CK10 ∷ CK10⁻ ∷ []) [] tt tt Eq.refl

wl0476 : Complete 4 → ⟪ (CS14⁻ ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0476 c4 = lw0 c4 (CS14⁻ ∷ CS14 ∷ []) [] tt tt Eq.refl

wl0477 : Complete 4 → ⟪ (S1 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0477 c4 = lw4 c4 (S1 ∷ S1⁻ ∷ []) [] tt tt Eq.refl

wl0478 : Complete 4 → ⟪ (S0⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S1⁻ ∷ []) ⟫ʷ
wl0478 c4 = lw4 c4 (S0⁻ ∷ Sw01 ∷ []) (Sw01 ∷ S1⁻ ∷ []) tt tt Eq.refl

wl0479 : Complete 4 → ⟪ (S1⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S0⁻ ∷ []) ⟫ʷ
wl0479 c4 = lw4 c4 (S1⁻ ∷ Sw01 ∷ []) (Sw01 ∷ S0⁻ ∷ []) tt tt Eq.refl

wl0480 : Complete 4 → ⟪ (S1⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S2⁻ ∷ []) ⟫ʷ
wl0480 c4 = lw4 c4 (S1⁻ ∷ Sw12 ∷ []) (Sw12 ∷ S2⁻ ∷ []) tt tt Eq.refl

wl0481 : Complete 4 → ⟪ (S2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S1⁻ ∷ []) ⟫ʷ
wl0481 c4 = lw4 c4 (S2⁻ ∷ Sw12 ∷ []) (Sw12 ∷ S1⁻ ∷ []) tt tt Eq.refl

wl0482 : Complete 4 → ⟪ (S2⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ S3⁻ ∷ []) ⟫ʷ
wl0482 c4 = lw4 c4 (S2⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S3⁻ ∷ []) tt tt Eq.refl

wl0483 : Complete 4 → ⟪ (S3⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ S2⁻ ∷ []) ⟫ʷ
wl0483 c4 = lw4 c4 (S3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S2⁻ ∷ []) tt tt Eq.refl

wl0484 : Complete 4 → ⟪ (S3⁻ ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ S4⁻ ∷ []) ⟫ʷ
wl0484 c4 = lw0 c4 (S3⁻ ∷ Sw34 ∷ []) (Sw34 ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0485 : Complete 4 → ⟪ (S4⁻ ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ S3⁻ ∷ []) ⟫ʷ
wl0485 c4 = lw0 c4 (S4⁻ ∷ Sw34 ∷ []) (Sw34 ∷ S3⁻ ∷ []) tt tt Eq.refl

wl0486 : Complete 4 → ⟪ (S4⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S4⁻ ∷ []) ⟫ʷ
wl0486 c4 = lw0 c4 (S4⁻ ∷ X1 ∷ []) (X1 ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0487 : Complete 4 → ⟪ (Toff012 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff012 ∷ []) ⟫ʷ
wl0487 c4 = lw4 c4 (Toff012 ∷ Toff312 ∷ []) (Toff312 ∷ Toff012 ∷ []) tt tt Eq.refl

wl0488 : Complete 4 → ⟪ (CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CZ34 ∷ []) ⟫ʷ
wl0488 c4 = lw0 c4 (CS34 ∷ CS34 ∷ []) (CZ34 ∷ []) tt tt Eq.refl

wl0489 : Complete 4 → ⟪ (CX24 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ CZ24 ∷ K4⁻ ∷ []) ⟫ʷ
wl0489 c4 = lw0 c4 (CX24 ∷ []) (K4 ∷ CZ24 ∷ K4⁻ ∷ []) tt tt Eq.refl

wl0490 : Complete 4 → ⟪ (CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ []) ⟫ʷ
wl0490 c4 = lw0 c4 (CS34⁻ ∷ []) (CS34⁻ ∷ []) tt tt Eq.refl

wl0491 : Complete 4 → ⟪ (CS14⁻ ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CS14⁻ ∷ []) ⟫ʷ
wl0491 c4 = lw0 c4 (CS14⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0492 : Complete 4 → ⟪ (CS34⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14 ∷ Toff423 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0492 c4 = lw0 c4 (CS34⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0493 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) ⟫ʷ
wl0493 c4 = lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) tt tt Eq.refl

wl0494 : Complete 4 → ⟪ (CS34 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS34 ∷ []) ⟫ʷ
wl0494 c4 = lw0 c4 (CS34 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS34 ∷ []) tt tt Eq.refl

wl0495 : Complete 4 → ⟪ (CS14 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS14 ∷ []) ⟫ʷ
wl0495 c4 = lw0 c4 (CS14 ∷ CS34 ∷ []) (CS34 ∷ CS14 ∷ []) tt tt Eq.refl

wl0496 : Complete 4 → ⟪ (CX32 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX32 ∷ []) ⟫ʷ
wl0496 c4 = lw4 c4 (CX32 ∷ Toff013 ∷ []) (Toff013 ∷ CX32 ∷ []) tt tt Eq.refl

wl0497 : Complete 4 → ⟪ (CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) ⟫ʷ
wl0497 c4 = lw0 c4 (CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ []) (Toff423 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) tt tt Eq.refl

wl0498 : Complete 4 → ⟪ (CS14⁻ ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0498 c4 = lw0 c4 (CS14⁻ ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0499 : Complete 4 → ⟪ (CS14 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14 ∷ []) ⟫ʷ
wl0499 c4 = lw0 c4 (CS14 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14 ∷ []) tt tt Eq.refl

wl0500 : Complete 4 → ⟪ (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) ⟫ʷ
wl0500 c4 = lw4 c4 (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff023 ∷ []) (Toff023 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) tt tt Eq.refl

wl0501 : Complete 4 → ⟪ (CCZ134 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ134 ∷ []) ⟫ʷ
wl0501 c4 = lw0 c4 (CCZ134 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0502 : Complete 4 → ⟪ (CCZ134 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ134 ∷ []) ⟫ʷ
wl0502 c4 = lw0 c4 (CCZ134 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0503 : Complete 4 → ⟪ (CCZ134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0503 c4 = lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl

wl0504 : Complete 4 → ⟪ (S0 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ S0 ∷ []) ⟫ʷ
wl0504 c4 = lw4 c4 (S0 ∷ Toff102 ∷ []) (Toff102 ∷ S0 ∷ []) tt tt Eq.refl

wl0505 : Complete 4 → ⟪ (CK41⁻ ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0505 c4 = lw0 c4 (CK41⁻ ∷ CK41 ∷ []) [] tt tt Eq.refl

wl0506 : Complete 4 → ⟪ (CK41 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4⁻ ∷ []) ⟫ʷ
wl0506 c4 = lw0 c4 (CK41 ∷ CK41 ∷ []) (S4⁻ ∷ []) tt tt Eq.refl

wl0507 : Complete 4 → ⟪ (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ []) ⟫ʷ
wl0507 c4 = lw4 c4 (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (ι ∷ []) tt tt Eq.refl

wl0508 : Complete 4 → ⟪ (K1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ
wl0508 c4 = lw4 c4 (K1 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) tt tt Eq.refl

wl0509 : Complete 4 → ⟪ (X0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0509 c4 = lw4 c4 (X0 ∷ X0 ∷ []) [] tt tt Eq.refl

wl0510 : Complete 4 → ⟪ (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wl0510 c4 = lw4 c4 (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wl0511 : Complete 4 → ⟪ (S0 ∷ X0 ∷ CS03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wl0511 c4 = lw4 c4 (S0 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wl0512 : Complete 4 → ⟪ (S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wl0512 c4 = lw4 c4 (S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wl0513 : Complete 4 → ⟪ (CS03⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0513 c4 = lw4 c4 (CS03⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0514 : Complete 4 → ⟪ (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) ⟫ʷ
wl0514 c4 = lw4 c4 (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) tt tt Eq.refl

wl0515 : Complete 4 → ⟪ (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wl0515 c4 = lw4 c4 (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wl0516 : Complete 4 → ⟪ (CK01 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) ⟫ʷ
wl0516 c4 = lw4 c4 (CK01 ∷ []) (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) tt tt Eq.refl

wl0517 : Complete 4 → ⟪ (CS01 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ
wl0517 c4 = lw4 c4 (CS01 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) tt tt Eq.refl

wl0518 : Complete 4 → ⟪ (CS01 ∷ X0 ∷ CS03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ
wl0518 c4 = lw4 c4 (CS01 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ []) tt tt Eq.refl

wl0519 : Complete 4 → ⟪ (CS01 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ []) ⟫ʷ
wl0519 c4 = lw4 c4 (CS01 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ []) tt tt Eq.refl

wl0520 : Complete 4 → ⟪ (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) ⟫ʷ
wl0520 c4 = lw4 c4 (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) tt tt Eq.refl

wl0521 : Complete 4 → ⟪ (CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS23 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ
wl0521 c4 = lw4 c4 (CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS01 ∷ []) tt tt Eq.refl

wl0522 : Complete 4 → ⟪ (CS01 ∷ X0 ∷ CX43 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ
wl0522 c4 = lw2 c4 (CS01 ∷ X0 ∷ CX43 ∷ X0 ∷ []) (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) tt tt Eq.refl

wl0523 : Complete 4 → ⟪ (CS01 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ []) ⟫ʷ
wl0523 c4 = lw4 c4 (CS01 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ []) tt tt Eq.refl

wl0524 : Complete 4 → ⟪ (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03⁻ ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) ⟫ʷ
wl0524 c4 = lw4 c4 (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) tt tt Eq.refl

wl0525 : Complete 4 → ⟪ (S0⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) ⟫ʷ
wl0525 c4 = lw4 c4 (S0⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) tt tt Eq.refl

wl0526 : Complete 4 → ⟪ (S0⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ []) ⟫ʷ
wl0526 c4 = lw4 c4 (S0⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ []) tt tt Eq.refl

wl0527 : Complete 4 → ⟪ (S0⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03⁻ ∷ X0 ∷ S0⁻ ∷ []) ⟫ʷ
wl0527 c4 = lw4 c4 (S0⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0⁻ ∷ []) tt tt Eq.refl

wl0528 : Complete 4 → ⟪ (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0528 c4 = lw4 c4 (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0529 : Complete 4 → ⟪ (CS03⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0529 c4 = lw4 c4 (CS03⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0530 : Complete 4 → ⟪ (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) ⟫ʷ
wl0530 c4 = lw4 c4 (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) tt tt Eq.refl

wl0531 : Complete 4 → ⟪ (CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) ⟫ʷ
wl0531 c4 = lw4 c4 (CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) tt tt Eq.refl

wl0532 : Complete 4 → ⟪ (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ
wl0532 c4 = lw4 c4 (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) tt tt Eq.refl

wl0533 : Complete 4 → ⟪ (CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ []) ⟫ʷ
wl0533 c4 = lw4 c4 (CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (K1⁻ ∷ []) tt tt Eq.refl

wl0534 : Complete 4 → ⟪ (S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (ι⁻ ∷ []) ⟫ʷ
wl0534 c4 = lw4 c4 (S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ []) (ι⁻ ∷ []) tt tt Eq.refl

wl0535 : Complete 4 → ⟪ (CK01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ []) ⟫ʷ
wl0535 c4 = lw4 c4 (CK01⁻ ∷ []) (CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ []) tt tt Eq.refl

wl0536 : Complete 4 → ⟪ (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ123 ∷ X0 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0536 c4 = lw4 c4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0537 : Complete 4 → ⟪ (CS01⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03⁻ ∷ X0 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0537 c4 = lw4 c4 (CS01⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0538 : Complete 4 → ⟪ (CS01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ X0 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0538 c4 = lw4 c4 (CS01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0539 : Complete 4 → ⟪ (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX43 ∷ X0 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0539 c4 = lw2 c4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (X0 ∷ CX43 ∷ X0 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0540 : Complete 4 → ⟪ (CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS23⁻ ∷ X0 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0540 c4 = lw4 c4 (CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0541 : Complete 4 → ⟪ (CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS23 ∷ X0 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0541 c4 = lw4 c4 (CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0542 : Complete 4 → ⟪ (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) ⟫ʷ
wl0542 c4 = lw4 c4 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0543 : Complete 4 → ⟪ (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) ⟫ʷ
wl0543 c4 = lw4 c4 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0544 : Complete 4 → ⟪ (CS03 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01⁻ ∷ X0 ∷ CS03 ∷ []) ⟫ʷ
wl0544 c4 = lw4 c4 (CS03 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ CS03 ∷ []) tt tt Eq.refl

wl0545 : Complete 4 → ⟪ (Toff201 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01⁻ ∷ X0 ∷ Toff201 ∷ []) ⟫ʷ
wl0545 c4 = lw4 c4 (Toff201 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ Toff201 ∷ []) tt tt Eq.refl

wl0546 : Complete 4 → ⟪ (CS03 ∷ X0 ∷ CS03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ X0 ∷ CS03 ∷ []) ⟫ʷ
wl0546 c4 = lw4 c4 (CS03 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS03 ∷ []) tt tt Eq.refl

wl0547 : Complete 4 → ⟪ (CS03⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ X0 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0547 c4 = lw4 c4 (CS03⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0548 : Complete 4 → ⟪ (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
wl0548 c4 = lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl

wl0549 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) ⟫ʷ
wl0549 c4 = lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) tt tt Eq.refl

wl0550 : Complete 4 → ⟪ (K2⁻ ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0550 c4 = lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl

wl0551 : Complete 4 → ⟪ (CCZ134 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CCZ134 ∷ []) ⟫ʷ
wl0551 c4 = lw0 c4 (CCZ134 ∷ K2 ∷ []) (K2 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0552 : Complete 4 → ⟪ (CS02 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13⁻ ∷ X0 ∷ CS02 ∷ []) ⟫ʷ
wl0552 c4 = lw4 c4 (CS02 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ CS13⁻ ∷ X0 ∷ CS02 ∷ []) tt tt Eq.refl

wl0553 : Complete 4 → ⟪ (CS02 ∷ X0 ∷ CS13 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13 ∷ X0 ∷ CS02 ∷ []) ⟫ʷ
wl0553 c4 = lw4 c4 (CS02 ∷ X0 ∷ CS13 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ X0 ∷ CS02 ∷ []) tt tt Eq.refl

wl0554 : Complete 4 → ⟪ (CCZ134 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ CCZ134 ∷ []) ⟫ʷ
wl0554 c4 = lw0 c4 (CCZ134 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0555 : Complete 4 → ⟪ (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) ⟫ʷ
wl0555 c4 = lw4 c4 (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0556 : Complete 4 → ⟪ (CS02⁻ ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13⁻ ∷ X0 ∷ CS02⁻ ∷ []) ⟫ʷ
wl0556 c4 = lw4 c4 (CS02⁻ ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ CS13⁻ ∷ X0 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl0557 : Complete 4 → ⟪ (CS02⁻ ∷ X0 ∷ CS13 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13 ∷ X0 ∷ CS02⁻ ∷ []) ⟫ʷ
wl0557 c4 = lw4 c4 (CS02⁻ ∷ X0 ∷ CS13 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ X0 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl0558 : Complete 4 → ⟪ (CCZ134 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ134 ∷ []) ⟫ʷ
wl0558 c4 = lw0 c4 (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0559 : Complete 4 → ⟪ (K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) ⟫ʷ
wl0559 c4 = lw4 c4 (K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0560 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) ⟫ʷ
wl0560 c4 = lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl

wl0561 : Complete 4 → ⟪ (K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) ⟫ʷ
wl0561 c4 = lw4 c4 (K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0562 : Complete 4 → ⟪ (K2 ∷ CS23 ∷ K2⁻ ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) ⟫ʷ
wl0562 c4 = lw0 c4 (K2 ∷ CS23 ∷ K2⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0563 : Complete 4 → ⟪ (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
wl0563 c4 = lw0 c4 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl

wl0564 : Complete 4 → ⟪ (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) ⟫ʷ
wl0564 c4 = lw4 c4 (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0565 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) ⟫ʷ
wl0565 c4 = lw0 c4 (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) tt tt Eq.refl

wl0566 : Complete 4 → ⟪ (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS12⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS12⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) ⟫ʷ
wl0566 c4 = lw4 c4 (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS12⁻ ∷ X0 ∷ []) (X0 ∷ CS12⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0567 : Complete 4 → ⟪ (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS12 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) ⟫ʷ
wl0567 c4 = lw4 c4 (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0568 : Complete 4 → ⟪ (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ K2 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) ⟫ʷ
wl0568 c4 = lw4 c4 (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ []) (X0 ∷ K2 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0569 : Complete 4 → ⟪ (K2 ∷ CS23⁻ ∷ K2⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ []) ⟫ʷ
wl0569 c4 = lw4 c4 (K2 ∷ CS23⁻ ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0570 : Complete 4 → ⟪ (K2 ∷ CS23⁻ ∷ K2⁻ ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ []) ⟫ʷ
wl0570 c4 = lw0 c4 (K2 ∷ CS23⁻ ∷ K2⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0571 : Complete 4 → ⟪ (Toff203 ∷ X0 ∷ CS02⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS02⁻ ∷ X0 ∷ Toff203 ∷ []) ⟫ʷ
wl0571 c4 = lw4 c4 (Toff203 ∷ X0 ∷ CS02⁻ ∷ X0 ∷ []) (X0 ∷ CS02⁻ ∷ X0 ∷ Toff203 ∷ []) tt tt Eq.refl

wl0572 : Complete 4 → ⟪ (Toff203 ∷ X0 ∷ CS02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS02 ∷ X0 ∷ Toff203 ∷ []) ⟫ʷ
wl0572 c4 = lw4 c4 (Toff203 ∷ X0 ∷ CS02 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ X0 ∷ Toff203 ∷ []) tt tt Eq.refl

wl0573 : Complete 4 → ⟪ (CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ []) ⟫ʷ
wl0573 c4 = lw4 c4 (CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ []) tt tt Eq.refl

wl0574 : Complete 4 → ⟪ (S0⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01⁻ ∷ X0 ∷ S0⁻ ∷ []) ⟫ʷ
wl0574 c4 = lw4 c4 (S0⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ S0⁻ ∷ []) tt tt Eq.refl

wl0575 : Complete 4 → ⟪ (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wl0575 c4 = lw4 c4 (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wl0576 : Complete 4 → ⟪ (CS03 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CS03 ∷ []) ⟫ʷ
wl0576 c4 = lw4 c4 (CS03 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS03 ∷ []) tt tt Eq.refl

wl0577 : Complete 4 → ⟪ (CS03⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0577 c4 = lw4 c4 (CS03⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0578 : Complete 4 → ⟪ (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ
wl0578 c4 = lw4 c4 (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) tt tt Eq.refl

wl0579 : Complete 4 → ⟪ (K2 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0579 c4 = lw4 c4 (K2 ∷ K2⁻ ∷ []) [] tt tt Eq.refl

wl0580 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ []) ⟫ʷ
wl0580 c4 = lw4 c4 (CCZ023 ∷ []) (K2⁻ ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ []) tt tt Eq.refl

wl0581 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) ⟫ʷ
wl0581 c4 = lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) tt tt Eq.refl

wl0582 : Complete 4 → ⟪ (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ123 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ []) ⟫ʷ
wl0582 c4 = lw4 c4 (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0583 : Complete 4 → ⟪ (CX20 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX20 ∷ []) ⟫ʷ
wl0583 c4 = lw4 c4 (CX20 ∷ X0 ∷ []) (X0 ∷ CX20 ∷ []) tt tt Eq.refl

wl0584 : Complete 4 → ⟪ (K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) ⟫ʷ
wl0584 c4 = lw4 c4 (K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0585 : Complete 4 → ⟪ (CS03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CS03 ∷ []) ⟫ʷ
wl0585 c4 = lw4 c4 (CS03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS03 ∷ []) tt tt Eq.refl

wl0586 : Complete 4 → ⟪ (CCZ123 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CCZ123 ∷ []) ⟫ʷ
wl0586 c4 = lw4 c4 (CCZ123 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0587 : Complete 4 → ⟪ (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03⁻ ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) ⟫ʷ
wl0587 c4 = lw4 c4 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0588 : Complete 4 → ⟪ (CK01⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK01⁻ ∷ []) ⟫ʷ
wl0588 c4 = lw4 c4 (CK01⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK01⁻ ∷ []) tt tt Eq.refl

wl0589 : Complete 4 → ⟪ (CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CK01⁻ ∷ []) ⟫ʷ
wl0589 c4 = lw4 c4 (CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CK01⁻ ∷ []) tt tt Eq.refl

wl0590 : Complete 4 → ⟪ (S0⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ S0⁻ ∷ []) ⟫ʷ
wl0590 c4 = lw4 c4 (S0⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ S0⁻ ∷ []) tt tt Eq.refl

wl0591 : Complete 4 → ⟪ (S0⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ S0⁻ ∷ []) ⟫ʷ
wl0591 c4 = lw4 c4 (S0⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ S0⁻ ∷ []) tt tt Eq.refl

wl0592 : Complete 4 → ⟪ (CK01 ∷ CK01⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0592 c4 = lw4 c4 (CK01 ∷ CK01⁻ ∷ []) [] tt tt Eq.refl

wl0593 : Complete 4 → ⟪ (S0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0593 c4 = lw4 c4 (S0 ∷ S0⁻ ∷ []) [] tt tt Eq.refl

wl0594 : Complete 4 → ⟪ (S4⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S4⁻ ∷ []) ⟫ʷ
wl0594 c4 = lw1 c4 (S4⁻ ∷ X0 ∷ []) (X0 ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0595 : Complete 4 → ⟪ (K2 ∷ CCZ023 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ []) ⟫ʷ
wl0595 c4 = lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0596 : Complete 4 → ⟪ (CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ []) ⟫ʷ
wl0596 c4 = lw0 c4 (CS24⁻ ∷ []) (CS24⁻ ∷ []) tt tt Eq.refl

wl0597 : Complete 4 → ⟪ (CS14⁻ ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CS14⁻ ∷ []) ⟫ʷ
wl0597 c4 = lw0 c4 (CS14⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0598 : Complete 4 → ⟪ (CS24⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14 ∷ Toff423 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0598 c4 = lw0 c4 (CS24⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0599 : Complete 4 → ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wl0599 c4 = lw4 c4 (Toff012 ∷ []) (Toff012 ∷ []) tt tt Eq.refl

wl0600 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) ⟫ʷ
wl0600 c4 = lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) tt tt Eq.refl

wl0601 : Complete 4 → ⟪ (CCZ012 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ012 ∷ []) ⟫ʷ
wl0601 c4 = lw4 c4 (CCZ012 ∷ CS23 ∷ []) (CS23 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0602 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) ⟫ʷ
wl0602 c4 = lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl

wl0603 : Complete 4 → ⟪ (CX21 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) ⟫ʷ
wl0603 c4 = lw0 c4 (CX21 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) tt tt Eq.refl

wl0604 : Complete 4 → ⟪ (Toff413 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0604 c4 = lw0 c4 (Toff413 ∷ Toff413 ∷ []) [] tt tt Eq.refl

wl0605 : Complete 4 → ⟪ (Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ []) ⟫ʷ
wl0605 c4 = lw0 c4 (Toff413 ∷ []) (Toff413 ∷ []) tt tt Eq.refl

wl0606 : Complete 4 → ⟪ (CCZ123 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ123 ∷ []) ⟫ʷ
wl0606 c4 = lw0 c4 (CCZ123 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0607 : Complete 4 → ⟪ (CS01⁻ ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS03 ∷ Toff312 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0607 c4 = lw4 c4 (CS01⁻ ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) (Toff312 ∷ CS03 ∷ Toff312 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0608 : Complete 4 → ⟪ (Toff023 ∷ CS01 ∷ Toff023 ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS03 ∷ Toff312 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) ⟫ʷ
wl0608 c4 = lw4 c4 (Toff023 ∷ CS01 ∷ Toff023 ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) (Toff312 ∷ CS03 ∷ Toff312 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) tt tt Eq.refl

wl0609 : Complete 4 → ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wl0609 c4 = lw4 c4 (Toff312 ∷ []) (Toff312 ∷ []) tt tt Eq.refl

wl0610 : Complete 4 → ⟪ (CCZ012 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ012 ∷ []) ⟫ʷ
wl0610 c4 = lw4 c4 (CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0611 : Complete 4 → ⟪ (CCZ012 ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS03 ∷ Toff312 ∷ CCZ012 ∷ []) ⟫ʷ
wl0611 c4 = lw4 c4 (CCZ012 ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) (Toff312 ∷ CS03 ∷ Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0612 : Complete 4 → ⟪ (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
wl0612 c4 = lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl

wl0613 : Complete 4 → ⟪ (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ []) ⟫ʷ
wl0613 c4 = lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) tt tt Eq.refl

wl0614 : Complete 4 → ⟪ (Toff124 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0614 c4 = lw0 c4 (Toff124 ∷ Toff124 ∷ []) [] tt tt Eq.refl

wl0615 : Complete 4 → ⟪ (Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
wl0615 c4 = lw0 c4 (Toff214 ∷ []) (Toff214 ∷ []) tt tt Eq.refl

wl0616 : Complete 4 → ⟪ (Toff324 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0616 c4 = lw0 c4 (Toff324 ∷ Toff324 ∷ []) [] tt tt Eq.refl

wl0617 : Complete 4 → ⟪ (CCZ124 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ124 ∷ []) ⟫ʷ
wl0617 c4 = lw0 c4 (CCZ124 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0618 : Complete 4 → ⟪ (Toff123 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0618 c4 = lw4 c4 (Toff123 ∷ Toff123 ∷ []) [] tt tt Eq.refl

wl0619 : Complete 4 → ⟪ (CCZ234 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CCZ234 ∷ []) ⟫ʷ
wl0619 c4 = lw0 c4 (CCZ234 ∷ Toff123 ∷ []) (Toff123 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0620 : Complete 4 → ⟪ (Toff234 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0620 c4 = lw0 c4 (Toff234 ∷ Toff234 ∷ []) [] tt tt Eq.refl

wl0621 : Complete 4 → ⟪ (Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ []) ⟫ʷ
wl0621 c4 = lw0 c4 (Toff234 ∷ []) (Toff234 ∷ []) tt tt Eq.refl

wl0622 : Complete 4 → ⟪ (Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
wl0622 c4 = lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl

wl0623 : Complete 4 → ⟪ (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0623 c4 = lw0 c4 (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ []) [] tt tt Eq.refl

wl0624 : Complete 4 → ⟪ (CCZ124 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ124 ∷ []) ⟫ʷ
wl0624 c4 = lw0 c4 (CCZ124 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0625 : Complete 4 → ⟪ (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
wl0625 c4 = lw0 c4 (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ []) tt tt Eq.refl

wl0626 : Complete 4 → ⟪ (CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ []) ⟫ʷ
wl0626 c4 = lw0 c4 (CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Toff234 ∷ []) tt tt Eq.refl

wl0627 : Complete 4 → ⟪ (Toff134 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0627 c4 = lw0 c4 (Toff134 ∷ Toff134 ∷ []) [] tt tt Eq.refl

wl0628 : Complete 4 → ⟪ (CCZ134 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) ⟫ʷ
wl0628 c4 = lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0629 : Complete 4 → ⟪ (CCZ124 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) ⟫ʷ
wl0629 c4 = lw0 c4 (CCZ124 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0630 : Complete 4 → ⟪ (CCZ124 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ124 ∷ []) ⟫ʷ
wl0630 c4 = lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0631 : Complete 4 → ⟪ (CCZ134 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ134 ∷ []) ⟫ʷ
wl0631 c4 = lw0 c4 (CCZ134 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0632 : Complete 4 → ⟪ (CCZ234 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ234 ∷ []) ⟫ʷ
wl0632 c4 = lw0 c4 (CCZ234 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0633 : Complete 4 → ⟪ (CCZ134 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CZ34 ∷ CCZ134 ∷ []) ⟫ʷ
wl0633 c4 = lw0 c4 (CCZ134 ∷ Toff134 ∷ []) (Toff134 ∷ CZ34 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0634 : Complete 4 → ⟪ (CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ
wl0634 c4 = lw0 c4 (CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0635 : Complete 4 → ⟪ (CCZ124 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ124 ∷ []) ⟫ʷ
wl0635 c4 = lw0 c4 (CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ []) tt tt Eq.refl

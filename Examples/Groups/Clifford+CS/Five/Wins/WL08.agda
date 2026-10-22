------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL08 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl1524 : Base 4 → ⟪ (CCZ012 ∷ CX23 ∷ CCZ012 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff302 ∷ []) ⟫ʷ
wl1524 c4 = lw4 c4 (CCZ012 ∷ CX23 ∷ CCZ012 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ []) tt tt Eq.refl

wl1525 : Base 4 → ⟪ (Toff302 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX23 ∷ Toff302 ∷ []) ⟫ʷ
wl1525 c4 = lw4 c4 (Toff302 ∷ X0 ∷ []) (X0 ∷ CX23 ∷ Toff302 ∷ []) tt tt Eq.refl

wl1526 : Base 4 → ⟪ (CS13 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13 ∷ []) ⟫ʷ
wl1526 c4 = lw4 c4 (CS13 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ []) tt tt Eq.refl

wl1527 : Base 4 → ⟪ (CS13 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS13 ∷ []) ⟫ʷ
wl1527 c4 = lw4 c4 (CS13 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS13 ∷ []) tt tt Eq.refl

wl1528 : Base 4 → ⟪ (CS13⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1528 c4 = lw4 c4 (CS13⁻ ∷ X0 ∷ []) (X0 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1529 : Base 4 → ⟪ (CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wl1529 c4 = lw4 c4 (CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1530 : Base 4 → ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1530 c4 = lw4 c4 (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1531 : Base 4 → ⟪ (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ
wl1531 c4 = lw4 c4 (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) tt tt Eq.refl

wl1532 : Base 4 → ⟪ (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ
wl1532 c4 = lw4 c4 (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CK02 ∷ []) tt tt Eq.refl

wl1533 : Base 4 → ⟪ (Toff423 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ Toff423 ∷ []) ⟫ʷ
wl1533 c4 = lw1 c4 (Toff423 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff423 ∷ []) tt tt Eq.refl

wl1534 : Base 4 → ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1534 c4 = lw4 c4 (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1535 : Base 4 → ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1535 c4 = lw4 c4 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1536 : Base 4 → ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ ι ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1536 c4 = lw4 c4 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1537 : Base 4 → ⟪ (K2 ∷ CK02 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ K2 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ
wl1537 c4 = lw4 c4 (K2 ∷ CK02 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ K2 ∷ CK02 ∷ S0 ∷ []) tt tt Eq.refl

wl1538 : Base 4 → ⟪ (K2 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ K2 ∷ []) ⟫ʷ
wl1538 c4 = lw0 c4 (K2 ∷ Toff413 ∷ []) (Toff413 ∷ K2 ∷ []) tt tt Eq.refl

wl1539 : Base 4 → ⟪ (CCZ123 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ []) ⟫ʷ
wl1539 c4 = lw4 c4 (CCZ123 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ []) (Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1540 : Base 4 → ⟪ (CCZ023 ∷ CS12 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff103 ∷ CCZ023 ∷ []) ⟫ʷ
wl1540 c4 = lw4 c4 (CCZ023 ∷ CS12 ∷ Toff103 ∷ []) (CS12 ∷ Toff103 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1541 : Base 4 → ⟪ (CX23 ∷ Toff302 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX23 ∷ Toff302 ∷ []) ⟫ʷ
wl1541 c4 = lw4 c4 (CX23 ∷ Toff302 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX23 ∷ Toff302 ∷ []) tt tt Eq.refl

wl1542 : Base 4 → ⟪ (CS13 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13 ∷ []) ⟫ʷ
wl1542 c4 = lw4 c4 (CS13 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13 ∷ []) tt tt Eq.refl

wl1543 : Base 4 → ⟪ (CS13⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wl1543 c4 = lw4 c4 (CS13⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1544 : Base 4 → ⟪ (CS12⁻ ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1544 c4 = lw0 c4 (CS12⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1545 : Base 4 → ⟪ (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ []) ⟫ʷ
wl1545 c4 = lw4 c4 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (Toff103 ∷ []) tt tt Eq.refl

wl1546 : Base 4 → ⟪ (CS23 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS23 ∷ []) ⟫ʷ
wl1546 c4 = lw0 c4 (CS23 ∷ Toff413 ∷ []) (Toff413 ∷ CS23 ∷ []) tt tt Eq.refl

wl1547 : Base 4 → ⟪ (CS12 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS12 ∷ []) ⟫ʷ
wl1547 c4 = lw0 c4 (CS12 ∷ Toff413 ∷ []) (Toff413 ∷ CS12 ∷ []) tt tt Eq.refl

wl1548 : Base 4 → ⟪ (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) ⟫ʷ
wl1548 c4 = lw4 c4 (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) tt tt Eq.refl

wl1549 : Base 4 → ⟪ (CCZ023 ∷ Toff103 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ CCZ023 ∷ []) ⟫ʷ
wl1549 c4 = lw4 c4 (CCZ023 ∷ Toff103 ∷ CS12 ∷ []) (Toff103 ∷ CS12 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1550 : Base 4 → ⟪ (CX31 ∷ Toff103 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX31 ∷ Toff103 ∷ []) ⟫ʷ
wl1550 c4 = lw4 c4 (CX31 ∷ Toff103 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX31 ∷ Toff103 ∷ []) tt tt Eq.refl

wl1551 : Base 4 → ⟪ (CX34 ∷ CX31 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX31 ∷ []) ⟫ʷ
wl1551 c4 = lw0 c4 (CX34 ∷ CX31 ∷ Toff413 ∷ []) (Toff413 ∷ CX31 ∷ []) tt tt Eq.refl

wl1552 : Base 4 → ⟪ (CX34 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX34 ∷ []) ⟫ʷ
wl1552 c4 = lw0 c4 (CX34 ∷ Toff413 ∷ []) (Toff413 ∷ CX34 ∷ []) tt tt Eq.refl

wl1553 : Base 4 → ⟪ (CCZ023 ∷ CX31 ∷ CCZ023 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Toff103 ∷ []) ⟫ʷ
wl1553 c4 = lw4 c4 (CCZ023 ∷ CX31 ∷ CCZ023 ∷ Toff103 ∷ []) (CX31 ∷ Toff103 ∷ []) tt tt Eq.refl

wl1554 : Base 4 → ⟪ (CS12 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS12 ∷ []) ⟫ʷ
wl1554 c4 = lw4 c4 (CS12 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS12 ∷ []) tt tt Eq.refl

wl1555 : Base 4 → ⟪ (CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wl1555 c4 = lw4 c4 (CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1556 : Base 4 → ⟪ (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wl1556 c4 = lw4 c4 (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wl1557 : Base 4 → ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ ι ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1557 c4 = lw4 c4 (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1558 : Base 4 → ⟪ (Toff423 ∷ ι ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ Toff423 ∷ []) ⟫ʷ
wl1558 c4 = lw1 c4 (Toff423 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff423 ∷ []) tt tt Eq.refl

wl1559 : Base 4 → ⟪ (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wl1559 c4 = lw4 c4 (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wl1560 : Base 4 → ⟪ (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ
wl1560 c4 = lw4 c4 (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CK02 ∷ []) tt tt Eq.refl

wl1561 : Base 4 → ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1561 c4 = lw4 c4 (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1562 : Base 4 → ⟪ (CCZ134 ∷ CX23 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ134 ∷ []) ⟫ʷ
wl1562 c4 = lw0 c4 (CCZ134 ∷ CX23 ∷ CCZ124 ∷ []) (CX23 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1563 : Base 4 → ⟪ (CX23 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
wl1563 c4 = lw0 c4 (CX23 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX23 ∷ []) tt tt Eq.refl

wl1564 : Base 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ012 ∷ CX23 ∷ []) ⟫ʷ
wl1564 c4 = lw4 c4 (CCZ012 ∷ []) (CX23 ∷ CCZ012 ∷ CX23 ∷ []) tt tt Eq.refl

wl1565 : Base 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ013 ∷ CX32 ∷ []) ⟫ʷ
wl1565 c4 = lw4 c4 (CCZ013 ∷ []) (CX32 ∷ CCZ013 ∷ CX32 ∷ []) tt tt Eq.refl

wl1566 : Base 4 → ⟪ (CCZ012 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ013 ∷ CCZ012 ∷ []) ⟫ʷ
wl1566 c4 = lw4 c4 (CCZ012 ∷ CX32 ∷ []) (CX32 ∷ CCZ013 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1567 : Base 4 → ⟪ (CCZ013 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) ⟫ʷ
wl1567 c4 = lw4 c4 (CCZ013 ∷ CX23 ∷ []) (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1568 : Base 4 → ⟪ (CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wl1568 c4 = lw4 c4 (CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl

wl1569 : Base 4 → ⟪ (CCZ124 ∷ CZ12 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
wl1569 c4 = lw0 c4 (CCZ124 ∷ CZ12 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1570 : Base 4 → ⟪ (CCZ124 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ Toff412 ∷ []) ⟫ʷ
wl1570 c4 = lw0 c4 (CCZ124 ∷ CZ12 ∷ []) (Toff412 ∷ CCZ124 ∷ Toff412 ∷ []) tt tt Eq.refl

wl1571 : Base 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ124 ∷ CZ12 ∷ []) ⟫ʷ
wl1571 c4 = lw0 c4 (CCZ124 ∷ []) (CZ12 ∷ CCZ124 ∷ CZ12 ∷ []) tt tt Eq.refl

wl1572 : Base 4 → ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1572 c4 = lw4 c4 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1573 : Base 4 → ⟪ (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ
wl1573 c4 = lw4 c4 (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ []) tt tt Eq.refl

wl1574 : Base 4 → ⟪ (K3 ∷ CK03 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ []) ⟫ʷ
wl1574 c4 = lw4 c4 (K3 ∷ CK03 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ []) tt tt Eq.refl

wl1575 : Base 4 → ⟪ (K3 ∷ CK03 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ
wl1575 c4 = lw4 c4 (K3 ∷ CK03 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ []) tt tt Eq.refl

wl1576 : Base 4 → ⟪ (CCZ124 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CCZ124 ∷ []) ⟫ʷ
wl1576 c4 = lw0 c4 (CCZ124 ∷ K3 ∷ []) (K3 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1577 : Base 4 → ⟪ (CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ
wl1577 c4 = lw4 c4 (CK03 ∷ X0 ∷ []) (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ []) tt tt Eq.refl

wl1578 : Base 4 → ⟪ (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ
wl1578 c4 = lw4 c4 (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) tt tt Eq.refl

wl1579 : Base 4 → ⟪ (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ
wl1579 c4 = lw4 c4 (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CK03 ∷ []) tt tt Eq.refl

wl1580 : Base 4 → ⟪ (CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ
wl1580 c4 = lw4 c4 (CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CK03 ∷ []) tt tt Eq.refl

wl1581 : Base 4 → ⟪ (K3 ∷ CK03 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ
wl1581 c4 = lw4 c4 (K3 ∷ CK03 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ []) tt tt Eq.refl

wl1582 : Base 4 → ⟪ (CK03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ
wl1582 c4 = lw4 c4 (CK03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK03 ∷ []) tt tt Eq.refl

wl1583 : Base 4 → ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1583 c4 = lw4 c4 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1584 : Base 4 → ⟪ (CK02 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ
wl1584 c4 = lw4 c4 (CK02 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK02 ∷ []) tt tt Eq.refl

wl1585 : Base 4 → ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1585 c4 = lw4 c4 (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1586 : Base 4 → ⟪ (CX32 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX32 ∷ []) ⟫ʷ
wl1586 c4 = lw0 c4 (CX32 ∷ Toff413 ∷ []) (Toff413 ∷ CX32 ∷ []) tt tt Eq.refl

wl1587 : Base 4 → ⟪ (CX23 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX23 ∷ Toff412 ∷ []) ⟫ʷ
wl1587 c4 = lw0 c4 (CX23 ∷ Toff413 ∷ []) (Toff413 ∷ CX23 ∷ Toff412 ∷ []) tt tt Eq.refl

wl1588 : Base 4 → ⟪ (CX12 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX12 ∷ []) ⟫ʷ
wl1588 c4 = lw0 c4 (CX12 ∷ Toff413 ∷ []) (Toff413 ∷ CX12 ∷ []) tt tt Eq.refl

wl1589 : Base 4 → ⟪ (Toff412 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff412 ∷ []) ⟫ʷ
wl1589 c4 = lw0 c4 (Toff412 ∷ Toff413 ∷ []) (Toff413 ∷ Toff412 ∷ []) tt tt Eq.refl

wl1590 : Base 4 → ⟪ (CX23 ∷ Toff412 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
wl1590 c4 = lw0 c4 (CX23 ∷ Toff412 ∷ Toff412 ∷ []) (CX23 ∷ []) tt tt Eq.refl

wl1591 : Base 4 → ⟪ (CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
wl1591 c4 = lw4 c4 (CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl

wl1592 : Base 4 → ⟪ (CCZ124 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ134 ∷ []) ⟫ʷ
wl1592 c4 = lw0 c4 (CCZ124 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1593 : Base 4 → ⟪ (Sw23 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw23 ∷ []) ⟫ʷ
wl1593 c4 = lw0 c4 (Sw23 ∷ Toff413 ∷ []) (Toff412 ∷ Sw23 ∷ []) tt tt Eq.refl

wl1594 : Base 4 → ⟪ (CCZ134 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ124 ∷ []) ⟫ʷ
wl1594 c4 = lw0 c4 (CCZ134 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1595 : Base 4 → ⟪ (Sw23 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Sw23 ∷ []) ⟫ʷ
wl1595 c4 = lw0 c4 (Sw23 ∷ Toff124 ∷ []) (Toff134 ∷ Sw23 ∷ []) tt tt Eq.refl

wl1596 : Base 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ []) ⟫ʷ
wl1596 c4 = lw0 c4 (CCZ124 ∷ []) (CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ []) tt tt Eq.refl

wl1597 : Base 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ023 ∷ CX01 ∷ []) ⟫ʷ
wl1597 c4 = lw4 c4 (CCZ023 ∷ []) (CX01 ∷ CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl

wl1598 : Base 4 → ⟪ (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ124 ∷ []) ⟫ʷ
wl1598 c4 = lw0 c4 (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (Toff413 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1599 : Base 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ123 ∷ CX10 ∷ []) ⟫ʷ
wl1599 c4 = lw4 c4 (CCZ123 ∷ []) (CX10 ∷ CCZ123 ∷ CX10 ∷ []) tt tt Eq.refl

wl1600 : Base 4 → ⟪ (CCZ023 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ123 ∷ CCZ023 ∷ []) ⟫ʷ
wl1600 c4 = lw4 c4 (CCZ023 ∷ CX10 ∷ []) (CX10 ∷ CCZ123 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1601 : Base 4 → ⟪ (CCZ123 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ023 ∷ CCZ123 ∷ []) ⟫ʷ
wl1601 c4 = lw4 c4 (CCZ123 ∷ CX01 ∷ []) (CX01 ∷ CCZ023 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1602 : Base 4 → ⟪ (CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
wl1602 c4 = lw4 c4 (CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl

wl1603 : Base 4 → ⟪ (CCZ124 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ124 ∷ CCZ123 ∷ []) ⟫ʷ
wl1603 c4 = lw0 c4 (CCZ124 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ124 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1604 : Base 4 → ⟪ (CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wl1604 c4 = lw4 c4 (CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl

wl1605 : Base 4 → ⟪ (K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ []) ⟫ʷ
wl1605 c4 = lw0 c4 (K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ []) (Toff413 ∷ []) tt tt Eq.refl

wl1606 : Base 4 → ⟪ (CS13⁻ ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1606 c4 = lw4 c4 (CS13⁻ ∷ Toff203 ∷ []) (Toff203 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1607 : Base 4 → ⟪ (CS13 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS13 ∷ []) ⟫ʷ
wl1607 c4 = lw4 c4 (CS13 ∷ Toff203 ∷ []) (Toff203 ∷ CS13 ∷ []) tt tt Eq.refl

wl1608 : Base 4 → ⟪ (Toff413 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ []) ⟫ʷ
wl1608 c4 = lw0 c4 (Toff413 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff413 ∷ []) tt tt Eq.refl

wl1609 : Base 4 → ⟪ (CX23 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CX23 ∷ []) ⟫ʷ
wl1609 c4 = lw0 c4 (CX23 ∷ Toff412 ∷ []) (Toff412 ∷ CX23 ∷ []) tt tt Eq.refl

wl1610 : Base 4 → ⟪ (CX32 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CX32 ∷ Toff413 ∷ []) ⟫ʷ
wl1610 c4 = lw0 c4 (CX32 ∷ Toff412 ∷ []) (Toff412 ∷ CX32 ∷ Toff413 ∷ []) tt tt Eq.refl

wl1611 : Base 4 → ⟪ (CX13 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CX13 ∷ []) ⟫ʷ
wl1611 c4 = lw0 c4 (CX13 ∷ Toff412 ∷ []) (Toff412 ∷ CX13 ∷ []) tt tt Eq.refl

wl1612 : Base 4 → ⟪ (CX32 ∷ Toff413 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
wl1612 c4 = lw0 c4 (CX32 ∷ Toff413 ∷ Toff413 ∷ []) (CX32 ∷ []) tt tt Eq.refl

wl1613 : Base 4 → ⟪ (Sw23 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sw23 ∷ []) ⟫ʷ
wl1613 c4 = lw0 c4 (Sw23 ∷ Toff412 ∷ []) (Toff413 ∷ Sw23 ∷ []) tt tt Eq.refl

wl1614 : Base 4 → ⟪ (Sw23 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Sw23 ∷ []) ⟫ʷ
wl1614 c4 = lw0 c4 (Sw23 ∷ Toff134 ∷ []) (Toff124 ∷ Sw23 ∷ []) tt tt Eq.refl

wl1615 : Base 4 → ⟪ (CS34 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS34 ∷ CS13 ∷ CCZ134 ∷ []) ⟫ʷ
wl1615 c4 = lw0 c4 (CS34 ∷ Toff413 ∷ []) (Toff413 ∷ CS34 ∷ CS13 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1616 : Base 4 → ⟪ (CCZ134 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CZ13 ∷ CCZ134 ∷ []) ⟫ʷ
wl1616 c4 = lw0 c4 (CCZ134 ∷ Toff413 ∷ []) (Toff413 ∷ CZ13 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1617 : Base 4 → ⟪ (CS34 ∷ CS13 ∷ CCZ134 ∷ CS13 ∷ CZ13 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ []) ⟫ʷ
wl1617 c4 = lw0 c4 (CS34 ∷ CS13 ∷ CCZ134 ∷ CS13 ∷ CZ13 ∷ CCZ134 ∷ []) (CS34 ∷ []) tt tt Eq.refl

wl1618 : Base 4 → ⟪ (CS34⁻ ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS34⁻ ∷ CS13⁻ ∷ CCZ134 ∷ []) ⟫ʷ
wl1618 c4 = lw0 c4 (CS34⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS34⁻ ∷ CS13⁻ ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1619 : Base 4 → ⟪ (CS34⁻ ∷ CS13⁻ ∷ CCZ134 ∷ CS13⁻ ∷ CZ13 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ []) ⟫ʷ
wl1619 c4 = lw0 c4 (CS34⁻ ∷ CS13⁻ ∷ CCZ134 ∷ CS13⁻ ∷ CZ13 ∷ CCZ134 ∷ []) (CS34⁻ ∷ []) tt tt Eq.refl

wl1620 : Base 4 → ⟪ (Toff103 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff103 ∷ Toff203 ∷ []) ⟫ʷ
wl1620 c4 = lw4 c4 (Toff103 ∷ Toff213 ∷ []) (Toff213 ∷ Toff103 ∷ Toff203 ∷ []) tt tt Eq.refl

wl1621 : Base 4 → ⟪ (Toff103 ∷ Toff203 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ []) ⟫ʷ
wl1621 c4 = lw4 c4 (Toff103 ∷ Toff203 ∷ Toff203 ∷ []) (Toff103 ∷ []) tt tt Eq.refl

wl1622 : Base 4 → ⟪ (CZ13 ∷ CCZ134 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ134 ∷ []) ⟫ʷ
wl1622 c4 = lw0 c4 (CZ13 ∷ CCZ134 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1623 : Base 4 → ⟪ (CX13 ∷ Toff301 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX13 ∷ Toff301 ∷ []) ⟫ʷ
wl1623 c4 = lw4 c4 (CX13 ∷ Toff301 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX13 ∷ Toff301 ∷ []) tt tt Eq.refl

wl1624 : Base 4 → ⟪ (CX14 ∷ CX13 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX13 ∷ []) ⟫ʷ
wl1624 c4 = lw0 c4 (CX14 ∷ CX13 ∷ Toff413 ∷ []) (Toff413 ∷ CX13 ∷ []) tt tt Eq.refl

wl1625 : Base 4 → ⟪ (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ []) ⟫ʷ
wl1625 c4 = lw4 c4 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (Toff301 ∷ []) tt tt Eq.refl

wl1626 : Base 4 → ⟪ (CX14 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX14 ∷ []) ⟫ʷ
wl1626 c4 = lw0 c4 (CX14 ∷ Toff413 ∷ []) (Toff413 ∷ CX14 ∷ []) tt tt Eq.refl

wl1627 : Base 4 → ⟪ (CCZ012 ∷ CX13 ∷ CCZ012 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ Toff301 ∷ []) ⟫ʷ
wl1627 c4 = lw4 c4 (CCZ012 ∷ CX13 ∷ CCZ012 ∷ Toff301 ∷ []) (CX13 ∷ Toff301 ∷ []) tt tt Eq.refl

wl1628 : Base 4 → ⟪ (CS12⁻ ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1628 c4 = lw0 c4 (CS12⁻ ∷ CS34 ∷ []) (CS34 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1629 : Base 4 → ⟪ (CS12 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS12 ∷ []) ⟫ʷ
wl1629 c4 = lw0 c4 (CS12 ∷ CS34 ∷ []) (CS34 ∷ CS12 ∷ []) tt tt Eq.refl

wl1630 : Base 4 → ⟪ (CS12⁻ ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wl1630 c4 = lw0 c4 (CS12⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1631 : Base 4 → ⟪ (CS12 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CS12 ∷ []) ⟫ʷ
wl1631 c4 = lw0 c4 (CS12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS12 ∷ []) tt tt Eq.refl

wl1632 : Base 4 → ⟪ (CK02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ K2⁻ ∷ CS02 ∷ K2 ∷ CS02 ∷ []) ⟫ʷ
wl1632 c4 = lw4 c4 (CK02⁻ ∷ []) (CS02 ∷ K2⁻ ∷ CS02 ∷ K2 ∷ CS02 ∷ []) tt tt Eq.refl

wl1633 : Base 4 → ⟪ (K2 ∷ CK02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
wl1633 c4 = lw4 c4 (K2 ∷ CK02⁻ ∷ []) (X0 ∷ CK02 ∷ X0 ∷ []) tt tt Eq.refl

wl1634 : Base 4 → ⟪ (Toff301 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ Toff301 ∷ []) ⟫ʷ
wl1634 c4 = lw4 c4 (Toff301 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff301 ∷ []) tt tt Eq.refl

wl1635 : Base 4 → ⟪ (CCZ123 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ
wl1635 c4 = lw4 c4 (CCZ123 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1636 : Base 4 → ⟪ (CCZ013 ∷ CCZ123 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ123 ∷ []) ⟫ʷ
wl1636 c4 = lw4 c4 (CCZ013 ∷ CCZ123 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1637 : Base 4 → ⟪ (CX23 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff301 ∷ CX23 ∷ []) ⟫ʷ
wl1637 c4 = lw4 c4 (CX23 ∷ Toff201 ∷ []) (Toff201 ∷ Toff301 ∷ CX23 ∷ []) tt tt Eq.refl

wl1638 : Base 4 → ⟪ (CCZ234 ∷ CZ24 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ234 ∷ []) ⟫ʷ
wl1638 c4 = lw0 c4 (CCZ234 ∷ CZ24 ∷ CX23 ∷ []) (CX23 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1639 : Base 4 → ⟪ (CCZ234 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ234 ∷ CX23 ∷ []) ⟫ʷ
wl1639 c4 = lw0 c4 (CCZ234 ∷ CZ24 ∷ []) (CX23 ∷ CCZ234 ∷ CX23 ∷ []) tt tt Eq.refl

wl1640 : Base 4 → ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
wl1640 c4 = lw4 c4 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2⁻ ∷ []) (Toff201 ∷ []) tt tt Eq.refl

wl1641 : Base 4 → ⟪ (Toff201 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff201 ∷ Toff301 ∷ []) ⟫ʷ
wl1641 c4 = lw4 c4 (Toff201 ∷ Toff312 ∷ []) (Toff312 ∷ Toff201 ∷ Toff301 ∷ []) tt tt Eq.refl

wl1642 : Base 4 → ⟪ (Toff201 ∷ Toff301 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
wl1642 c4 = lw4 c4 (Toff201 ∷ Toff301 ∷ Toff301 ∷ []) (Toff201 ∷ []) tt tt Eq.refl

wl1643 : Base 4 → ⟪ (CS34⁻ ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ []) ⟫ʷ
wl1643 c4 = lw0 c4 (CS34⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1644 : Base 4 → ⟪ (CS24⁻ ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS24⁻ ∷ []) ⟫ʷ
wl1644 c4 = lw0 c4 (CS24⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl1645 : Base 4 → ⟪ (CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ CS24⁻ ∷ CZ24 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ []) ⟫ʷ
wl1645 c4 = lw0 c4 (CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ CS24⁻ ∷ CZ24 ∷ CCZ234 ∷ []) (CS34⁻ ∷ []) tt tt Eq.refl

wl1646 : Base 4 → ⟪ (CX23 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX23 ∷ []) ⟫ʷ
wl1646 c4 = lw4 c4 (CX23 ∷ Toff301 ∷ []) (Toff301 ∷ CX23 ∷ []) tt tt Eq.refl

wl1647 : Base 4 → ⟪ (CS34 ∷ CS24 ∷ CCZ234 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CS34 ∷ []) ⟫ʷ
wl1647 c4 = lw0 c4 (CS34 ∷ CS24 ∷ CCZ234 ∷ CX23 ∷ []) (CX23 ∷ CS34 ∷ []) tt tt Eq.refl

wl1648 : Base 4 → ⟪ (CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CS34⁻ ∷ []) ⟫ʷ
wl1648 c4 = lw0 c4 (CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ CX23 ∷ []) (CX23 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl1649 : Base 4 → ⟪ (CCZ234 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ234 ∷ []) ⟫ʷ
wl1649 c4 = lw0 c4 (CCZ234 ∷ CS24 ∷ []) (CS24 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1650 : Base 4 → ⟪ (CS24 ∷ CS34⁻ ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ []) ⟫ʷ
wl1650 c4 = lw0 c4 (CS24 ∷ CS34⁻ ∷ CS24⁻ ∷ []) (CS34⁻ ∷ []) tt tt Eq.refl

wl1651 : Base 4 → ⟪ (CCZ234 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CCZ234 ∷ []) ⟫ʷ
wl1651 c4 = lw0 c4 (CCZ234 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1652 : Base 4 → ⟪ (CS34 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS34 ∷ CS24 ∷ CCZ234 ∷ []) ⟫ʷ
wl1652 c4 = lw0 c4 (CS34 ∷ Toff324 ∷ []) (Toff324 ∷ CS34 ∷ CS24 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1653 : Base 4 → ⟪ (CS24 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS24 ∷ []) ⟫ʷ
wl1653 c4 = lw0 c4 (CS24 ∷ Toff324 ∷ []) (Toff324 ∷ CS24 ∷ []) tt tt Eq.refl

wl1654 : Base 4 → ⟪ (CS34 ∷ CS24 ∷ CCZ234 ∷ CS24 ∷ CZ24 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ []) ⟫ʷ
wl1654 c4 = lw0 c4 (CS34 ∷ CS24 ∷ CCZ234 ∷ CS24 ∷ CZ24 ∷ CCZ234 ∷ []) (CS34 ∷ []) tt tt Eq.refl

wl1655 : Base 4 → ⟪ (CX32 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX32 ∷ Toff201 ∷ []) ⟫ʷ
wl1655 c4 = lw4 c4 (CX32 ∷ Toff301 ∷ []) (Toff301 ∷ CX32 ∷ Toff201 ∷ []) tt tt Eq.refl

wl1656 : Base 4 → ⟪ (CS34 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CS34 ∷ []) ⟫ʷ
wl1656 c4 = lw0 c4 (CS34 ∷ CX32 ∷ []) (CX32 ∷ CS34 ∷ []) tt tt Eq.refl

wl1657 : Base 4 → ⟪ (CX32 ∷ Toff201 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX32 ∷ []) ⟫ʷ
wl1657 c4 = lw4 c4 (CX32 ∷ Toff201 ∷ Toff301 ∷ []) (Toff301 ∷ CX32 ∷ []) tt tt Eq.refl

wl1658 : Base 4 → ⟪ (CS34⁻ ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CS34⁻ ∷ []) ⟫ʷ
wl1658 c4 = lw0 c4 (CS34⁻ ∷ CX32 ∷ []) (CX32 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl1659 : Base 4 → ⟪ (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) ⟫ʷ
wl1659 c4 = lw0 c4 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) tt tt Eq.refl

wl1660 : Base 4 → ⟪ (Sw23 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Sw23 ∷ []) ⟫ʷ
wl1660 c4 = lw4 c4 (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ []) tt tt Eq.refl

wl1661 : Base 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ023 ∷ CX31 ∷ []) ⟫ʷ
wl1661 c4 = lw4 c4 (CCZ023 ∷ []) (CX31 ∷ CCZ023 ∷ CX31 ∷ []) tt tt Eq.refl

wl1662 : Base 4 → ⟪ (CX13 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CX13 ∷ Toff412 ∷ []) ⟫ʷ
wl1662 c4 = lw0 c4 (CX13 ∷ Toff423 ∷ []) (Toff423 ∷ CX13 ∷ Toff412 ∷ []) tt tt Eq.refl

wl1663 : Base 4 → ⟪ (CX21 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CX21 ∷ []) ⟫ʷ
wl1663 c4 = lw0 c4 (CX21 ∷ Toff423 ∷ []) (Toff423 ∷ CX21 ∷ []) tt tt Eq.refl

wl1664 : Base 4 → ⟪ (CX13 ∷ Toff412 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
wl1664 c4 = lw0 c4 (CX13 ∷ Toff412 ∷ Toff412 ∷ []) (CX13 ∷ []) tt tt Eq.refl

wl1665 : Base 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ012 ∷ CX13 ∷ []) ⟫ʷ
wl1665 c4 = lw4 c4 (CCZ012 ∷ []) (CX13 ∷ CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl

wl1666 : Base 4 → ⟪ (CCZ023 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ012 ∷ CCZ023 ∷ []) ⟫ʷ
wl1666 c4 = lw4 c4 (CCZ023 ∷ CX13 ∷ []) (CX13 ∷ CCZ012 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1667 : Base 4 → ⟪ (CCZ012 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ023 ∷ CCZ012 ∷ []) ⟫ʷ
wl1667 c4 = lw4 c4 (CCZ012 ∷ CX31 ∷ []) (CX31 ∷ CCZ023 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1668 : Base 4 → ⟪ (CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
wl1668 c4 = lw4 c4 (CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl

wl1669 : Base 4 → ⟪ (CCZ124 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Sw13 ∷ CCZ234 ∷ []) ⟫ʷ
wl1669 c4 = lw0 c4 (CCZ124 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1670 : Base 4 → ⟪ (Sw13 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw13 ∷ []) ⟫ʷ
wl1670 c4 = lw0 c4 (Sw13 ∷ Toff423 ∷ []) (Toff412 ∷ Sw13 ∷ []) tt tt Eq.refl

wl1671 : Base 4 → ⟪ (CCZ234 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Sw13 ∷ CCZ124 ∷ []) ⟫ʷ
wl1671 c4 = lw0 c4 (CCZ234 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1672 : Base 4 → ⟪ (Sw13 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Sw13 ∷ []) ⟫ʷ
wl1672 c4 = lw0 c4 (Sw13 ∷ Toff214 ∷ []) (Toff234 ∷ Sw13 ∷ []) tt tt Eq.refl

wl1673 : Base 4 → ⟪ (CCZ134 ∷ Toff412 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ134 ∷ []) ⟫ʷ
wl1673 c4 = lw0 c4 (CCZ134 ∷ Toff412 ∷ CCZ123 ∷ []) (Toff412 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1674 : Base 4 → ⟪ (K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ []) ⟫ʷ
wl1674 c4 = lw0 c4 (K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ []) (Toff412 ∷ []) tt tt Eq.refl

wl1675 : Base 4 → ⟪ (CS12⁻ ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1675 c4 = lw4 c4 (CS12⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1676 : Base 4 → ⟪ (Toff412 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ []) ⟫ʷ
wl1676 c4 = lw0 c4 (Toff412 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff412 ∷ []) tt tt Eq.refl

wl1677 : Base 4 → ⟪ (CX31 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CX31 ∷ Toff423 ∷ []) ⟫ʷ
wl1677 c4 = lw0 c4 (CX31 ∷ Toff412 ∷ []) (Toff412 ∷ CX31 ∷ Toff423 ∷ []) tt tt Eq.refl

wl1678 : Base 4 → ⟪ (CX31 ∷ Toff423 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
wl1678 c4 = lw0 c4 (CX31 ∷ Toff423 ∷ Toff423 ∷ []) (CX31 ∷ []) tt tt Eq.refl

wl1679 : Base 4 → ⟪ (CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wl1679 c4 = lw4 c4 (CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl

wl1680 : Base 4 → ⟪ (Sw13 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sw13 ∷ []) ⟫ʷ
wl1680 c4 = lw0 c4 (Sw13 ∷ Toff412 ∷ []) (Toff423 ∷ Sw13 ∷ []) tt tt Eq.refl

wl1681 : Base 4 → ⟪ (Sw13 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw13 ∷ []) ⟫ʷ
wl1681 c4 = lw0 c4 (Sw13 ∷ Toff234 ∷ []) (Toff214 ∷ Sw13 ∷ []) tt tt Eq.refl

wl1682 : Base 4 → ⟪ (CS24 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS24 ∷ CS23 ∷ CCZ234 ∷ []) ⟫ʷ
wl1682 c4 = lw0 c4 (CS24 ∷ Toff423 ∷ []) (Toff423 ∷ CS24 ∷ CS23 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1683 : Base 4 → ⟪ (CCZ234 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CZ23 ∷ CCZ234 ∷ []) ⟫ʷ
wl1683 c4 = lw0 c4 (CCZ234 ∷ Toff423 ∷ []) (Toff423 ∷ CZ23 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1684 : Base 4 → ⟪ (CS23 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS23 ∷ []) ⟫ʷ
wl1684 c4 = lw0 c4 (CS23 ∷ Toff423 ∷ []) (Toff423 ∷ CS23 ∷ []) tt tt Eq.refl

wl1685 : Base 4 → ⟪ (CS24 ∷ CS23 ∷ CCZ234 ∷ CS23 ∷ CZ23 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ []) ⟫ʷ
wl1685 c4 = lw0 c4 (CS24 ∷ CS23 ∷ CCZ234 ∷ CS23 ∷ CZ23 ∷ CCZ234 ∷ []) (CS24 ∷ []) tt tt Eq.refl

wl1686 : Base 4 → ⟪ (CS24⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS24⁻ ∷ CS23⁻ ∷ CCZ234 ∷ []) ⟫ʷ
wl1686 c4 = lw0 c4 (CS24⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS24⁻ ∷ CS23⁻ ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1687 : Base 4 → ⟪ (CS23⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS23⁻ ∷ []) ⟫ʷ
wl1687 c4 = lw0 c4 (CS23⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS23⁻ ∷ []) tt tt Eq.refl

wl1688 : Base 4 → ⟪ (CS24⁻ ∷ CS23⁻ ∷ CCZ234 ∷ CS23⁻ ∷ CZ23 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ []) ⟫ʷ
wl1688 c4 = lw0 c4 (CS24⁻ ∷ CS23⁻ ∷ CCZ234 ∷ CS23⁻ ∷ CZ23 ∷ CCZ234 ∷ []) (CS24⁻ ∷ []) tt tt Eq.refl

wl1689 : Base 4 → ⟪ (CZ34 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CZ34 ∷ CCZ124 ∷ []) ⟫ʷ
wl1689 c4 = lw0 c4 (CZ34 ∷ Toff312 ∷ []) (Toff312 ∷ CZ34 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1690 : Base 4 → ⟪ (X0 ∷ CZ34 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wl1690 c4 = lw1 c4 (X0 ∷ CZ34 ∷ CZ34 ∷ []) (X0 ∷ []) tt tt Eq.refl

wl1691 : Base 4 → ⟪ (CCZ124 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ124 ∷ CCZ123 ∷ []) ⟫ʷ
wl1691 c4 = lw0 c4 (CCZ124 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ124 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1692 : Base 4 → ⟪ (CCZ124 ∷ CCZ123 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ124 ∷ []) ⟫ʷ
wl1692 c4 = lw0 c4 (CCZ124 ∷ CCZ123 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1693 : Base 4 → ⟪ (CX12 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff201 ∷ []) ⟫ʷ
wl1693 c4 = lw4 c4 (CX12 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ []) tt tt Eq.refl

wl1694 : Base 4 → ⟪ (CX12 ∷ Toff201 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX12 ∷ Toff201 ∷ []) ⟫ʷ
wl1694 c4 = lw4 c4 (CX12 ∷ Toff201 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX12 ∷ Toff201 ∷ []) tt tt Eq.refl

wl1695 : Base 4 → ⟪ (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
wl1695 c4 = lw4 c4 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (Toff201 ∷ []) tt tt Eq.refl

wl1696 : Base 4 → ⟪ (Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX12 ∷ Toff201 ∷ []) ⟫ʷ
wl1696 c4 = lw4 c4 (Toff201 ∷ X0 ∷ []) (X0 ∷ CX12 ∷ Toff201 ∷ []) tt tt Eq.refl

wl1697 : Base 4 → ⟪ (CS24 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS24 ∷ []) ⟫ʷ
wl1697 c4 = lw1 c4 (CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ []) tt tt Eq.refl

wl1698 : Base 4 → ⟪ (CS13⁻ ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1698 c4 = lw0 c4 (CS13⁻ ∷ CS24 ∷ []) (CS24 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1699 : Base 4 → ⟪ (CS13 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS13 ∷ []) ⟫ʷ
wl1699 c4 = lw0 c4 (CS13 ∷ CS24 ∷ []) (CS24 ∷ CS13 ∷ []) tt tt Eq.refl

wl1700 : Base 4 → ⟪ (CS24⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS24⁻ ∷ []) ⟫ʷ
wl1700 c4 = lw1 c4 (CS24⁻ ∷ X0 ∷ []) (X0 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl1701 : Base 4 → ⟪ (CS13 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CS13 ∷ []) ⟫ʷ
wl1701 c4 = lw0 c4 (CS13 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13 ∷ []) tt tt Eq.refl

wl1702 : Base 4 → ⟪ (Toff203 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ Toff203 ∷ []) ⟫ʷ
wl1702 c4 = lw4 c4 (Toff203 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff203 ∷ []) tt tt Eq.refl

wl1703 : Base 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1703 c4 = lw4 c4 (CCZ012 ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1704 : Base 4 → ⟪ (CK02 ∷ CCZ012 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
wl1704 c4 = lw4 c4 (CK02 ∷ CCZ012 ∷ CK02 ∷ S0 ∷ []) (Toff201 ∷ []) tt tt Eq.refl

wl1705 : Base 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1705 c4 = lw4 c4 (CCZ023 ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1706 : Base 4 → ⟪ (CK03 ∷ CCZ023 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
wl1706 c4 = lw4 c4 (CK03 ∷ CCZ023 ∷ CK03 ∷ S0 ∷ []) (Toff302 ∷ []) tt tt Eq.refl

wl1707 : Base 4 → ⟪ (CK02 ∷ CCZ023 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
wl1707 c4 = lw4 c4 (CK02 ∷ CCZ023 ∷ CK02 ∷ S0 ∷ []) (Toff203 ∷ []) tt tt Eq.refl

wl1708 : Base 4 → ⟪ (K2 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
wl1708 c4 = lw4 c4 (K2 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl

wl1709 : Base 4 → ⟪ (K2⁻ ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ K2⁻ ∷ []) ⟫ʷ
wl1709 c4 = lw0 c4 (K2⁻ ∷ Toff413 ∷ []) (Toff413 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl1710 : Base 4 → ⟪ (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
wl1710 c4 = lw4 c4 (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl

wl1711 : Base 4 → ⟪ (CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ []) ⟫ʷ
wl1711 c4 = lw4 c4 (CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ []) (CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ []) tt tt Eq.refl

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

wl0505 : Complete 4 → ⟪ (CCZ123 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff312 ∷ []) ⟫ʷ
wl0505 c4 = lw4 c4 (CCZ123 ∷ CZ12 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff312 ∷ []) tt tt Eq.refl

wl0506 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ123 ∷ CZ12 ∷ []) ⟫ʷ
wl0506 c4 = lw4 c4 (CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ CZ12 ∷ []) tt tt Eq.refl

wl0507 : Complete 4 → ⟪ (CCZ234 ∷ Toff412 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ234 ∷ []) ⟫ʷ
wl0507 c4 = lw0 c4 (CCZ234 ∷ Toff412 ∷ CCZ123 ∷ []) (Toff412 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0508 : Complete 4 → ⟪ (CCZ123 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ123 ∷ []) ⟫ʷ
wl0508 c4 = lw0 c4 (CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0509 : Complete 4 → ⟪ (CX02 ∷ CX20 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Sw02 ∷ []) ⟫ʷ
wl0509 c4 = lw4 c4 (CX02 ∷ CX20 ∷ CX02 ∷ []) (Sw02 ∷ []) tt tt Eq.refl

wl0510 : Complete 4 → ⟪ (CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
wl0510 c4 = lw4 c4 (CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl

wl0511 : Complete 4 → ⟪ (CX34 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff412 ∷ CX34 ∷ []) ⟫ʷ
wl0511 c4 = lw0 c4 (CX34 ∷ Toff312 ∷ []) (Toff312 ∷ Toff412 ∷ CX34 ∷ []) tt tt Eq.refl

wl0512 : Complete 4 → ⟪ (CZ03 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) ⟫ʷ
wl0512 c4 = lw4 c4 (CZ03 ∷ Toff312 ∷ []) (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0513 : Complete 4 → ⟪ (Toff312 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff312 ∷ []) ⟫ʷ
wl0513 c4 = lw0 c4 (Toff312 ∷ Toff412 ∷ []) (Toff412 ∷ Toff312 ∷ []) tt tt Eq.refl

wl0514 : Complete 4 → ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wl0514 c4 = lw4 c4 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl

wl0515 : Complete 4 → ⟪ (Toff312 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff312 ∷ Toff412 ∷ []) ⟫ʷ
wl0515 c4 = lw0 c4 (Toff312 ∷ Toff423 ∷ []) (Toff423 ∷ Toff312 ∷ Toff412 ∷ []) tt tt Eq.refl

wl0516 : Complete 4 → ⟪ (Toff412 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff412 ∷ []) ⟫ʷ
wl0516 c4 = lw0 c4 (Toff412 ∷ Toff423 ∷ []) (Toff423 ∷ Toff412 ∷ []) tt tt Eq.refl

wl0517 : Complete 4 → ⟪ (Toff312 ∷ Toff412 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wl0517 c4 = lw0 c4 (Toff312 ∷ Toff412 ∷ Toff412 ∷ []) (Toff312 ∷ []) tt tt Eq.refl

wl0518 : Complete 4 → ⟪ (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
wl0518 c4 = lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl

wl0519 : Complete 4 → ⟪ (CCZ013 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ CZ01 ∷ []) ⟫ʷ
wl0519 c4 = lw4 c4 (CCZ013 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ013 ∷ CZ01 ∷ []) tt tt Eq.refl

wl0520 : Complete 4 → ⟪ (CCZ013 ∷ CZ01 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ []) ⟫ʷ
wl0520 c4 = lw4 c4 (CCZ013 ∷ CZ01 ∷ Toff301 ∷ CCZ013 ∷ []) (Toff301 ∷ []) tt tt Eq.refl

wl0521 : Complete 4 → ⟪ (CX02 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX02 ∷ []) ⟫ʷ
wl0521 c4 = lw4 c4 (CX02 ∷ Toff301 ∷ []) (Toff301 ∷ CX02 ∷ []) tt tt Eq.refl

wl0522 : Complete 4 → ⟪ (CX20 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX20 ∷ Toff312 ∷ []) ⟫ʷ
wl0522 c4 = lw4 c4 (CX20 ∷ Toff301 ∷ []) (Toff301 ∷ CX20 ∷ Toff312 ∷ []) tt tt Eq.refl

wl0523 : Complete 4 → ⟪ (CCZ234 ∷ Toff312 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ234 ∷ []) ⟫ʷ
wl0523 c4 = lw0 c4 (CCZ234 ∷ Toff312 ∷ CCZ124 ∷ []) (Toff312 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0524 : Complete 4 → ⟪ (CX12 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX12 ∷ []) ⟫ʷ
wl0524 c4 = lw4 c4 (CX12 ∷ Toff301 ∷ []) (Toff301 ∷ CX12 ∷ []) tt tt Eq.refl

wl0525 : Complete 4 → ⟪ (Toff301 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff301 ∷ []) ⟫ʷ
wl0525 c4 = lw4 c4 (Toff301 ∷ Toff312 ∷ []) (Toff312 ∷ Toff301 ∷ []) tt tt Eq.refl

wl0526 : Complete 4 → ⟪ (CX20 ∷ Toff312 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
wl0526 c4 = lw4 c4 (CX20 ∷ Toff312 ∷ Toff312 ∷ []) (CX20 ∷ []) tt tt Eq.refl

wl0527 : Complete 4 → ⟪ (CCZ124 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ124 ∷ []) ⟫ʷ
wl0527 c4 = lw0 c4 (CCZ124 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0528 : Complete 4 → ⟪ (CCZ123 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Sw02 ∷ CCZ013 ∷ []) ⟫ʷ
wl0528 c4 = lw4 c4 (CCZ123 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0529 : Complete 4 → ⟪ (Sw02 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Sw02 ∷ []) ⟫ʷ
wl0529 c4 = lw4 c4 (Sw02 ∷ Toff301 ∷ []) (Toff312 ∷ Sw02 ∷ []) tt tt Eq.refl

wl0530 : Complete 4 → ⟪ (CCZ013 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Sw02 ∷ CCZ123 ∷ []) ⟫ʷ
wl0530 c4 = lw4 c4 (CCZ013 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0531 : Complete 4 → ⟪ (Sw02 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ Sw02 ∷ []) ⟫ʷ
wl0531 c4 = lw4 c4 (Sw02 ∷ Toff123 ∷ []) (Toff103 ∷ Sw02 ∷ []) tt tt Eq.refl

wl0532 : Complete 4 → ⟪ (CCZ124 ∷ Toff412 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
wl0532 c4 = lw0 c4 (CCZ124 ∷ Toff412 ∷ CZ12 ∷ []) (Toff412 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0533 : Complete 4 → ⟪ (CCZ124 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CZ12 ∷ CCZ124 ∷ []) ⟫ʷ
wl0533 c4 = lw0 c4 (CCZ124 ∷ Toff412 ∷ []) (Toff412 ∷ CZ12 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0534 : Complete 4 → ⟪ (CX20 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX20 ∷ []) ⟫ʷ
wl0534 c4 = lw4 c4 (CX20 ∷ Toff312 ∷ []) (Toff312 ∷ CX20 ∷ []) tt tt Eq.refl

wl0535 : Complete 4 → ⟪ (CCZ234 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ234 ∷ CCZ124 ∷ []) ⟫ʷ
wl0535 c4 = lw0 c4 (CCZ234 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ234 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0536 : Complete 4 → ⟪ (CX02 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX02 ∷ Toff301 ∷ []) ⟫ʷ
wl0536 c4 = lw4 c4 (CX02 ∷ Toff312 ∷ []) (Toff312 ∷ CX02 ∷ Toff301 ∷ []) tt tt Eq.refl

wl0537 : Complete 4 → ⟪ (CX10 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX10 ∷ []) ⟫ʷ
wl0537 c4 = lw4 c4 (CX10 ∷ Toff312 ∷ []) (Toff312 ∷ CX10 ∷ []) tt tt Eq.refl

wl0538 : Complete 4 → ⟪ (CX02 ∷ Toff301 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
wl0538 c4 = lw4 c4 (CX02 ∷ Toff301 ∷ Toff301 ∷ []) (CX02 ∷ []) tt tt Eq.refl

wl0539 : Complete 4 → ⟪ (Sw02 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Sw02 ∷ []) ⟫ʷ
wl0539 c4 = lw4 c4 (Sw02 ∷ Toff312 ∷ []) (Toff301 ∷ Sw02 ∷ []) tt tt Eq.refl

wl0540 : Complete 4 → ⟪ (Sw02 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ Sw02 ∷ []) ⟫ʷ
wl0540 c4 = lw4 c4 (Sw02 ∷ Toff103 ∷ []) (Toff123 ∷ Sw02 ∷ []) tt tt Eq.refl

wl0541 : Complete 4 → ⟪ (CX34 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0541 c4 = lw0 c4 (CX34 ∷ CX34 ∷ []) [] tt tt Eq.refl

wl0542 : Complete 4 → ⟪ (CS14⁻ ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0542 c4 = lw0 c4 (CS14⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0543 : Complete 4 → ⟪ (CS14 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS14 ∷ []) ⟫ʷ
wl0543 c4 = lw0 c4 (CS14 ∷ Toff324 ∷ []) (Toff324 ∷ CS14 ∷ []) tt tt Eq.refl

wl0544 : Complete 4 → ⟪ (CX43 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX43 ∷ []) ⟫ʷ
wl0544 c4 = lw0 c4 (CX43 ∷ Toff324 ∷ []) (Toff324 ∷ CX43 ∷ []) tt tt Eq.refl

wl0545 : Complete 4 → ⟪ (CX43 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CX43 ∷ Toff312 ∷ []) ⟫ʷ
wl0545 c4 = lw0 c4 (CX43 ∷ Toff412 ∷ []) (Toff412 ∷ CX43 ∷ Toff312 ∷ []) tt tt Eq.refl

wl0546 : Complete 4 → ⟪ (CX43 ∷ Toff312 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CX43 ∷ []) ⟫ʷ
wl0546 c4 = lw0 c4 (CX43 ∷ Toff312 ∷ Toff412 ∷ []) (Toff412 ∷ CX43 ∷ []) tt tt Eq.refl

wl0547 : Complete 4 → ⟪ (CX34 ∷ CX43 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ []) ⟫ʷ
wl0547 c4 = lw0 c4 (CX34 ∷ CX43 ∷ CX34 ∷ []) (Sw34 ∷ []) tt tt Eq.refl

wl0548 : Complete 4 → ⟪ (Sw34 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Sw34 ∷ []) ⟫ʷ
wl0548 c4 = lw0 c4 (Sw34 ∷ Toff412 ∷ []) (Toff312 ∷ Sw34 ∷ []) tt tt Eq.refl

wl0549 : Complete 4 → ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0549 c4 = lw0 c4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0550 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0550 c4 = lw0 c4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0551 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0551 c4 = lw0 c4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0552 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0552 c4 = lw0 c4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0553 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0553 c4 = lw0 c4 (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0554 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0554 c4 = lw0 c4 (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0555 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0555 c4 = lw0 c4 (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0556 : Complete 4 → ⟪ (Toff213 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ Toff213 ∷ []) ⟫ʷ
wl0556 c4 = lw0 c4 (Toff213 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff213 ∷ []) tt tt Eq.refl

wl0557 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ []) ⟫ʷ
wl0557 c4 = lw1 c4 (X4 ∷ S4 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0558 : Complete 4 → ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0558 c4 = lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0559 : Complete 4 → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0559 c4 = lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0560 : Complete 4 → ⟪ (CCZ023 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ023 ∷ []) ⟫ʷ
wl0560 c4 = lw4 c4 (CCZ023 ∷ CX01 ∷ []) (CX01 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0561 : Complete 4 → ⟪ (CCZ023 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CCZ023 ∷ []) ⟫ʷ
wl0561 c4 = lw4 c4 (CCZ023 ∷ S0 ∷ []) (S0 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0562 : Complete 4 → ⟪ (CCZ013 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CCZ013 ∷ []) ⟫ʷ
wl0562 c4 = lw4 c4 (CCZ013 ∷ S0 ∷ []) (S0 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0563 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0563 c4 = lw0 c4 (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0564 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0564 c4 = lw0 c4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0565 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0565 c4 = lw0 c4 (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0566 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0566 c4 = lw0 c4 (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0567 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0567 c4 = lw0 c4 (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0568 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0568 c4 = lw0 c4 (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0569 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0569 c4 = lw0 c4 (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0570 : Complete 4 → ⟪ (Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ Toff213 ∷ []) ⟫ʷ
wl0570 c4 = lw0 c4 (Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff213 ∷ []) tt tt Eq.refl

wl0571 : Complete 4 → ⟪ (S1 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
wl0571 c4 = lw0 c4 (S1 ∷ CS14⁻ ∷ []) (X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl

wl0572 : Complete 4 → ⟪ (S1 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ S1 ∷ []) ⟫ʷ
wl0572 c4 = lw4 c4 (S1 ∷ Toff023 ∷ []) (Toff023 ∷ S1 ∷ []) tt tt Eq.refl

wl0573 : Complete 4 → ⟪ (S1 ∷ CS14⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S1 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0573 c4 = lw0 c4 (S1 ∷ CS14⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0574 : Complete 4 → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0574 c4 = lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0575 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0575 c4 = lw0 c4 (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0576 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0576 c4 = lw0 c4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0577 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0577 c4 = lw0 c4 (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0578 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0578 c4 = lw0 c4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0579 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0579 c4 = lw0 c4 (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0580 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0580 c4 = lw0 c4 (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0581 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0581 c4 = lw0 c4 (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0582 : Complete 4 → ⟪ (CCZ123 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CCZ123 ∷ []) ⟫ʷ
wl0582 c4 = lw4 c4 (CCZ123 ∷ S2 ∷ []) (S2 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0583 : Complete 4 → ⟪ (S2 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
wl0583 c4 = lw0 c4 (S2 ∷ CS24⁻ ∷ []) (X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl

wl0584 : Complete 4 → ⟪ (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ []) ⟫ʷ
wl0584 c4 = lw0 c4 (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0585 : Complete 4 → ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0585 c4 = lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0586 : Complete 4 → ⟪ (S2 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ S2 ∷ []) ⟫ʷ
wl0586 c4 = lw4 c4 (S2 ∷ Toff013 ∷ []) (Toff013 ∷ S2 ∷ []) tt tt Eq.refl

wl0587 : Complete 4 → ⟪ (S2 ∷ CS24⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0587 c4 = lw0 c4 (S2 ∷ CS24⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S2 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0588 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0588 c4 = lw0 c4 (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0589 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0589 c4 = lw0 c4 (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0590 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0590 c4 = lw0 c4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0591 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0591 c4 = lw0 c4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0592 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0592 c4 = lw0 c4 (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0593 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0593 c4 = lw0 c4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0594 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0594 c4 = lw0 c4 (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0595 : Complete 4 → ⟪ (Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ Toff213 ∷ []) ⟫ʷ
wl0595 c4 = lw0 c4 (Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff213 ∷ []) tt tt Eq.refl

wl0596 : Complete 4 → ⟪ (S3 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
wl0596 c4 = lw0 c4 (S3 ∷ CS34⁻ ∷ []) (X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl

wl0597 : Complete 4 → ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0597 c4 = lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0598 : Complete 4 → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0598 c4 = lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0599 : Complete 4 → ⟪ (K0 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ K0 ∷ []) ⟫ʷ
wl0599 c4 = lw4 c4 (K0 ∷ CCZ023 ∷ []) (Toff023 ∷ K0 ∷ []) tt tt Eq.refl

wl0600 : Complete 4 → ⟪ (K0⁻ ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ K0⁻ ∷ []) ⟫ʷ
wl0600 c4 = lw4 c4 (K0⁻ ∷ CCZ023 ∷ []) (Toff023 ∷ K0⁻ ∷ []) tt tt Eq.refl

wl0601 : Complete 4 → ⟪ (K0 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ K0 ∷ []) ⟫ʷ
wl0601 c4 = lw4 c4 (K0 ∷ CCZ013 ∷ []) (Toff013 ∷ K0 ∷ []) tt tt Eq.refl

wl0602 : Complete 4 → ⟪ (K0⁻ ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ K0⁻ ∷ []) ⟫ʷ
wl0602 c4 = lw4 c4 (K0⁻ ∷ CCZ013 ∷ []) (Toff013 ∷ K0⁻ ∷ []) tt tt Eq.refl

wl0603 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0603 c4 = lw0 c4 (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0604 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0604 c4 = lw0 c4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0605 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0605 c4 = lw0 c4 (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0606 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0606 c4 = lw0 c4 (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0607 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0607 c4 = lw0 c4 (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0608 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0608 c4 = lw0 c4 (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0609 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0609 c4 = lw0 c4 (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0610 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) ⟫ʷ
wl0610 c4 = lw0 c4 (CCZ123 ∷ []) (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) tt tt Eq.refl

wl0611 : Complete 4 → ⟪ (CCZ123 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl0611 c4 = lw4 c4 (CCZ123 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0612 : Complete 4 → ⟪ (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ123 ∷ []) ⟫ʷ
wl0612 c4 = lw4 c4 (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) (CX01 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0613 : Complete 4 → ⟪ (CCZ023 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ023 ∷ []) ⟫ʷ
wl0613 c4 = lw4 c4 (CCZ023 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0614 : Complete 4 → ⟪ (CX01 ∷ CCZ023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
wl0614 c4 = lw4 c4 (CX01 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX01 ∷ []) tt tt Eq.refl

wl0615 : Complete 4 → ⟪ (CCZ123 ∷ Toff214 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ123 ∷ []) ⟫ʷ
wl0615 c4 = lw0 c4 (CCZ123 ∷ Toff214 ∷ CCZ134 ∷ []) (Toff214 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0616 : Complete 4 → ⟪ (CCZ123 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ123 ∷ []) ⟫ʷ
wl0616 c4 = lw4 c4 (CCZ123 ∷ CX10 ∷ []) (CX10 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0617 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) ⟫ʷ
wl0617 c4 = lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) tt tt Eq.refl

wl0618 : Complete 4 → ⟪ (CCZ123 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ123 ∷ []) ⟫ʷ
wl0618 c4 = lw0 c4 (CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0619 : Complete 4 → ⟪ (CX01 ∷ CX10 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ []) ⟫ʷ
wl0619 c4 = lw4 c4 (CX01 ∷ CX10 ∷ CX01 ∷ []) (Sw01 ∷ []) tt tt Eq.refl

wl0620 : Complete 4 → ⟪ (CCZ023 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wl0620 c4 = lw4 c4 (CCZ023 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0621 : Complete 4 → ⟪ (CCZ023 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ023 ∷ []) ⟫ʷ
wl0621 c4 = lw4 c4 (CCZ023 ∷ CS12 ∷ []) (CS12 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0622 : Complete 4 → ⟪ (CCZ124 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ CZ14 ∷ []) ⟫ʷ
wl0622 c4 = lw0 c4 (CCZ124 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ124 ∷ CZ14 ∷ []) tt tt Eq.refl

wl0623 : Complete 4 → ⟪ (CCZ124 ∷ CZ14 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
wl0623 c4 = lw0 c4 (CCZ124 ∷ CZ14 ∷ Toff214 ∷ CCZ124 ∷ []) (Toff214 ∷ []) tt tt Eq.refl

wl0624 : Complete 4 → ⟪ (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
wl0624 c4 = lw0 c4 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl

wl0625 : Complete 4 → ⟪ (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
wl0625 c4 = lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl

wl0626 : Complete 4 → ⟪ (CCZ023 ∷ CZ03 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
wl0626 c4 = lw4 c4 (CCZ023 ∷ CZ03 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0627 : Complete 4 → ⟪ (CCZ023 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ Toff203 ∷ []) ⟫ʷ
wl0627 c4 = lw4 c4 (CCZ023 ∷ CZ03 ∷ []) (Toff203 ∷ CCZ023 ∷ Toff203 ∷ []) tt tt Eq.refl

wl0628 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CCZ023 ∷ CZ03 ∷ []) ⟫ʷ
wl0628 c4 = lw4 c4 (CCZ023 ∷ []) (CZ03 ∷ CCZ023 ∷ CZ03 ∷ []) tt tt Eq.refl

wl0629 : Complete 4 → ⟪ (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ []) ⟫ʷ
wl0629 c4 = lw0 c4 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0630 : Complete 4 → ⟪ (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
wl0630 c4 = lw4 c4 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0631 : Complete 4 → ⟪ (CS03⁻ ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
wl0631 c4 = lw4 c4 (CS03⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0632 : Complete 4 → ⟪ (CS03⁻ ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0632 c4 = lw4 c4 (CS03⁻ ∷ S2 ∷ []) (S2 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0633 : Complete 4 → ⟪ (CS14⁻ ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0633 c4 = lw0 c4 (CS14⁻ ∷ S2 ∷ []) (S2 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0634 : Complete 4 → ⟪ (CS14⁻ ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CS14⁻ ∷ []) ⟫ʷ
wl0634 c4 = lw0 c4 (CS14⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0635 : Complete 4 → ⟪ (Toff203 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0635 c4 = lw4 c4 (Toff203 ∷ Toff203 ∷ []) [] tt tt Eq.refl

wl0636 : Complete 4 → ⟪ (Toff214 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0636 c4 = lw0 c4 (Toff214 ∷ Toff214 ∷ []) [] tt tt Eq.refl

wl0637 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) ⟫ʷ
wl0637 c4 = lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl

wl0638 : Complete 4 → ⟪ (CCZ124 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ124 ∷ []) ⟫ʷ
wl0638 c4 = lw0 c4 (CCZ124 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0639 : Complete 4 → ⟪ (CCZ124 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ124 ∷ []) ⟫ʷ
wl0639 c4 = lw0 c4 (CCZ124 ∷ CS23 ∷ []) (CS23 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0640 : Complete 4 → ⟪ (CCZ023 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ CZ03 ∷ []) ⟫ʷ
wl0640 c4 = lw4 c4 (CCZ023 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ023 ∷ CZ03 ∷ []) tt tt Eq.refl

wl0641 : Complete 4 → ⟪ (CCZ023 ∷ CZ03 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
wl0641 c4 = lw4 c4 (CCZ023 ∷ CZ03 ∷ Toff203 ∷ CCZ023 ∷ []) (Toff203 ∷ []) tt tt Eq.refl

wl0642 : Complete 4 → ⟪ (Toff214 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ Toff214 ∷ []) ⟫ʷ
wl0642 c4 = lw0 c4 (Toff214 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff214 ∷ []) tt tt Eq.refl

wl0643 : Complete 4 → ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0643 c4 = lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0644 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) ⟫ʷ
wl0644 c4 = lw0 c4 (CCZ124 ∷ []) (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) tt tt Eq.refl

wl0645 : Complete 4 → ⟪ (CCZ013 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ013 ∷ []) ⟫ʷ
wl0645 c4 = lw4 c4 (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0646 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ124 ∷ CX43 ∷ []) ⟫ʷ
wl0646 c4 = lw0 c4 (CCZ124 ∷ []) (CX43 ∷ CCZ124 ∷ CX43 ∷ []) tt tt Eq.refl

wl0647 : Complete 4 → ⟪ (CCZ013 ∷ Toff023 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ013 ∷ []) ⟫ʷ
wl0647 c4 = lw4 c4 (CCZ013 ∷ Toff023 ∷ CCZ123 ∷ []) (Toff023 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0648 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ123 ∷ CX34 ∷ []) ⟫ʷ
wl0648 c4 = lw0 c4 (CCZ123 ∷ []) (CX34 ∷ CCZ123 ∷ CX34 ∷ []) tt tt Eq.refl

wl0649 : Complete 4 → ⟪ (CX43 ∷ CX34 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ []) ⟫ʷ
wl0649 c4 = lw0 c4 (CX43 ∷ CX34 ∷ CX43 ∷ []) (Sw34 ∷ []) tt tt Eq.refl

wl0650 : Complete 4 → ⟪ (CCZ124 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) ⟫ʷ
wl0650 c4 = lw0 c4 (CCZ124 ∷ CX34 ∷ []) (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0651 : Complete 4 → ⟪ (CCZ124 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ124 ∷ []) ⟫ʷ
wl0651 c4 = lw0 c4 (CCZ124 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0652 : Complete 4 → ⟪ (CCZ123 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) ⟫ʷ
wl0652 c4 = lw0 c4 (CCZ123 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0653 : Complete 4 → ⟪ (CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wl0653 c4 = lw0 c4 (CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wl0654 : Complete 4 → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0654 c4 = lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0655 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0655 c4 = lw0 c4 (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0656 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0656 c4 = lw0 c4 (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0657 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0657 c4 = lw0 c4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0658 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0658 c4 = lw0 c4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0659 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0659 c4 = lw0 c4 (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0660 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0660 c4 = lw0 c4 (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0661 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0661 c4 = lw0 c4 (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0662 : Complete 4 → ⟪ (K2 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ K2 ∷ []) ⟫ʷ
wl0662 c4 = lw4 c4 (K2 ∷ CCZ123 ∷ []) (Toff213 ∷ K2 ∷ []) tt tt Eq.refl

wl0663 : Complete 4 → ⟪ (K2⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ K2⁻ ∷ []) ⟫ʷ
wl0663 c4 = lw4 c4 (K2⁻ ∷ CCZ123 ∷ []) (Toff213 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0664 : Complete 4 → ⟪ (CK42⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ K2⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ []) ⟫ʷ
wl0664 c4 = lw0 c4 (CK42⁻ ∷ []) (CS24 ∷ K2⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ []) tt tt Eq.refl

wl0665 : Complete 4 → ⟪ (K2 ∷ CK42⁻ ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
wl0665 c4 = lw0 c4 (K2 ∷ CK42⁻ ∷ []) (X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl

wl0666 : Complete 4 → ⟪ (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ Toff314 ∷ []) ⟫ʷ
wl0666 c4 = lw0 c4 (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0667 : Complete 4 → ⟪ (CCZ023 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wl0667 c4 = lw4 c4 (CCZ023 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0668 : Complete 4 → ⟪ (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ023 ∷ []) ⟫ʷ
wl0668 c4 = lw4 c4 (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (CX12 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0669 : Complete 4 → ⟪ (CCZ023 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wl0669 c4 = lw4 c4 (CCZ023 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0670 : Complete 4 → ⟪ (CCZ023 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ023 ∷ []) ⟫ʷ
wl0670 c4 = lw4 c4 (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0671 : Complete 4 → ⟪ (CCZ013 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ013 ∷ []) ⟫ʷ
wl0671 c4 = lw4 c4 (CCZ013 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0672 : Complete 4 → ⟪ (CX12 ∷ CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
wl0672 c4 = lw4 c4 (CX12 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX12 ∷ []) tt tt Eq.refl

wl0673 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ134 ∷ CX12 ∷ []) ⟫ʷ
wl0673 c4 = lw0 c4 (CCZ134 ∷ []) (CX12 ∷ CCZ134 ∷ CX12 ∷ []) tt tt Eq.refl

wl0674 : Complete 4 → ⟪ (CCZ023 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ023 ∷ []) ⟫ʷ
wl0674 c4 = lw4 c4 (CCZ023 ∷ CX21 ∷ []) (CX21 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0675 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) ⟫ʷ
wl0675 c4 = lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) tt tt Eq.refl

wl0676 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ234 ∷ CX21 ∷ []) ⟫ʷ
wl0676 c4 = lw0 c4 (CCZ234 ∷ []) (CX21 ∷ CCZ234 ∷ CX21 ∷ []) tt tt Eq.refl

wl0677 : Complete 4 → ⟪ (CX12 ∷ CX21 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ []) ⟫ʷ
wl0677 c4 = lw4 c4 (CX12 ∷ CX21 ∷ CX12 ∷ []) (Sw12 ∷ []) tt tt Eq.refl

wl0678 : Complete 4 → ⟪ (CCZ134 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) ⟫ʷ
wl0678 c4 = lw0 c4 (CCZ134 ∷ CX21 ∷ []) (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0679 : Complete 4 → ⟪ (CCZ134 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ134 ∷ []) ⟫ʷ
wl0679 c4 = lw0 c4 (CCZ134 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0680 : Complete 4 → ⟪ (CCZ234 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) ⟫ʷ
wl0680 c4 = lw0 c4 (CCZ234 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0681 : Complete 4 → ⟪ (CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wl0681 c4 = lw0 c4 (CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wl0682 : Complete 4 → ⟪ (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
wl0682 c4 = lw4 c4 (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0683 : Complete 4 → ⟪ (CCZ013 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff013 ∷ []) ⟫ʷ
wl0683 c4 = lw4 c4 (CCZ013 ∷ CZ13 ∷ []) (Toff013 ∷ CCZ013 ∷ Toff013 ∷ []) tt tt Eq.refl

wl0684 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ013 ∷ CZ13 ∷ []) ⟫ʷ
wl0684 c4 = lw4 c4 (CCZ013 ∷ []) (CZ13 ∷ CCZ013 ∷ CZ13 ∷ []) tt tt Eq.refl

wl0685 : Complete 4 → ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0685 c4 = lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0686 : Complete 4 → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0686 c4 = lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0687 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0687 c4 = lw0 c4 (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0688 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0688 c4 = lw0 c4 (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0689 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0689 c4 = lw0 c4 (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0690 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0690 c4 = lw0 c4 (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0691 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0691 c4 = lw0 c4 (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0692 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0692 c4 = lw0 c4 (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0693 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0693 c4 = lw0 c4 (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0694 : Complete 4 → ⟪ (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ123 ∷ []) ⟫ʷ
wl0694 c4 = lw0 c4 (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) (CX41 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0695 : Complete 4 → ⟪ (CX41 ∷ CCZ234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wl0695 c4 = lw0 c4 (CX41 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wl0696 : Complete 4 → ⟪ (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ123 ∷ []) ⟫ʷ
wl0696 c4 = lw4 c4 (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) (Toff201 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0697 : Complete 4 → ⟪ (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ []) ⟫ʷ
wl0697 c4 = lw0 c4 (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ []) tt tt Eq.refl

wl0698 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) ⟫ʷ
wl0698 c4 = lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) tt tt Eq.refl

wl0699 : Complete 4 → ⟪ (CCZ023 ∷ Toff012 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ023 ∷ []) ⟫ʷ
wl0699 c4 = lw4 c4 (CCZ023 ∷ Toff012 ∷ CCZ123 ∷ []) (Toff012 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0700 : Complete 4 → ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0700 c4 = lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the four-wire derivations, each decided once
--
-- Each lemma is one window step of Four/D: two words on three wires with
-- the same operator, equal by completeness on three wires
-- (Windows.win, one evaluation, through the tables of Four.Lits),
-- stated over the macro letters as Four/D uses it.  Written by
-- scratchpad/four/winlib4.py, restated by winmac4.py and wintable4.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Wins.W29 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)

wn01512 : Base 3 → ⟪ (CCZ012 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CZ02 ∷ CCZ012 ∷ []) ⟫ʷ
wn01512 b = lw3 b (CCZ012 ∷ Toff102 ∷ []) (Toff102 ∷ CZ02 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01513 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01513 b = lw3 b (CS02 ∷ CS02 ∷ CZ02 ∷ []) [] tt tt Eq.refl
wn01514 : Base 3 → ⟪ (CS12⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn01514 b = lw3 b (CS12⁻ ∷ Toff102 ∷ []) (Toff102 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01515 : Base 3 → ⟪ (CS02⁻ ∷ CS02⁻ ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01515 b = lw3 b (CS02⁻ ∷ CS02⁻ ∷ CZ02 ∷ []) [] tt tt Eq.refl
wn01516 : Base 3 → ⟪ (X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CZ01 ∷ CCZ012 ∷ K1⁻ ∷ []) ⟫ʷ
wn01516 b = lw3 b (X2 ∷ Toff102 ∷ X2 ∷ []) (K1 ∷ CZ01 ∷ CCZ012 ∷ K1⁻ ∷ []) tt tt Eq.refl
wn01517 : Base 3 → ⟪ (K1 ∷ CZ01 ∷ CCZ012 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ
wn01517 b = lw3 b (K1 ∷ CZ01 ∷ CCZ012 ∷ K1⁻ ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ []) tt tt Eq.refl
wn01518 : Base 3 → ⟪ (S1 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ S1 ∷ CS02 ∷ CCZ012 ∷ []) ⟫ʷ
wn01518 b = lw3 b (S1 ∷ Toff102 ∷ []) (Toff102 ∷ S1 ∷ CS02 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01519 : Base 3 → ⟪ (S1⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ S1⁻ ∷ CS02⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn01519 b = lw3 b (S1⁻ ∷ Toff102 ∷ []) (Toff102 ∷ S1⁻ ∷ CS02⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01520 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CS23 ∷ CS23⁻ ∷ []) ⟫ʷ
wn01520 b = lw0 b [] (CS23 ∷ CS23⁻ ∷ []) tt tt Eq.refl
wn01521 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff201 ∷ []) ⟫ʷ
wn01521 b = lw3 b [] (Toff201 ∷ Toff201 ∷ []) tt tt Eq.refl
wn01522 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS23 ∷ []) ⟫ʷ
wn01522 b = lw0 b [] (CS23⁻ ∷ CS23 ∷ []) tt tt Eq.refl
wn01523 : Base 3 → ⟪ (CS23⁻ ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01523 b = lw0 b (CS23⁻ ∷ CS23 ∷ []) [] tt tt Eq.refl
wn01524 : Base 3 → ⟪ (Toff201 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01524 b = lw3 b (Toff201 ∷ Toff201 ∷ []) [] tt tt Eq.refl
wn01525 : Base 3 → ⟪ (CS23 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01525 b = lw0 b (CS23 ∷ CS23⁻ ∷ []) [] tt tt Eq.refl
wn01526 : Base 3 → ⟪ (CS02 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS01 ∷ CS02 ∷ CCZ012 ∷ []) ⟫ʷ
wn01526 b = lw3 b (CS02 ∷ Toff201 ∷ []) (Toff201 ∷ CS01 ∷ CS02 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01527 : Base 3 → ⟪ (CCZ012 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CZ01 ∷ CCZ012 ∷ []) ⟫ʷ
wn01527 b = lw3 b (CCZ012 ∷ Toff201 ∷ []) (Toff201 ∷ CZ01 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01528 : Base 3 → ⟪ (CS01 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS01 ∷ []) ⟫ʷ
wn01528 b = lw3 b (CS01 ∷ Toff201 ∷ []) (Toff201 ∷ CS01 ∷ []) tt tt Eq.refl
wn01529 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01529 b = lw3 b (CS01 ∷ CS01 ∷ CZ01 ∷ []) [] tt tt Eq.refl
wn01530 : Base 3 → ⟪ (CS02⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS01⁻ ∷ CS02⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn01530 b = lw3 b (CS02⁻ ∷ Toff201 ∷ []) (Toff201 ∷ CS01⁻ ∷ CS02⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01531 : Base 3 → ⟪ (CS01⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS01⁻ ∷ []) ⟫ʷ
wn01531 b = lw3 b (CS01⁻ ∷ Toff201 ∷ []) (Toff201 ∷ CS01⁻ ∷ []) tt tt Eq.refl
wn01532 : Base 3 → ⟪ (CS01⁻ ∷ CS01⁻ ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01532 b = lw3 b (CS01⁻ ∷ CS01⁻ ∷ CZ01 ∷ []) [] tt tt Eq.refl
wn01533 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01533 b = lw3 b (X2 ∷ CK21 ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) tt tt Eq.refl
wn01534 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn01534 b = lw0 b (X3 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ []) tt tt Eq.refl
wn01535 : Base 3 → ⟪ (Toff201 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) ⟫ʷ
wn01535 b = lw3 b (Toff201 ∷ []) (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) tt tt Eq.refl
wn01536 : Base 3 → ⟪ (K2⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ K2⁻ ∷ []) ⟫ʷ
wn01536 b = lw0 b (K2⁻ ∷ CS13 ∷ []) (CS13 ∷ K2⁻ ∷ []) tt tt Eq.refl
wn01537 : Base 3 → ⟪ (K2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ K2 ∷ []) ⟫ʷ
wn01537 b = lw0 b (K2 ∷ CS13 ∷ []) (CS13 ∷ K2 ∷ []) tt tt Eq.refl
wn01538 : Base 3 → ⟪ (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
wn01538 b = lw3 b (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (Toff201 ∷ []) tt tt Eq.refl
wn01539 : Base 3 → ⟪ (S2 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ S2 ∷ CS01 ∷ CCZ012 ∷ []) ⟫ʷ
wn01539 b = lw3 b (S2 ∷ Toff201 ∷ []) (Toff201 ∷ S2 ∷ CS01 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01540 : Base 3 → ⟪ (S2⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ S2⁻ ∷ CS01⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn01540 b = lw3 b (S2⁻ ∷ Toff201 ∷ []) (Toff201 ∷ S2⁻ ∷ CS01⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01541 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01541 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01542 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01542 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01543 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01543 b = lw3 b (X2 ∷ CK20⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01544 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01544 b = lw3 b (X2 ∷ CK20⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01545 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01545 b = lw3 b (X2 ∷ CK20 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn01546 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01546 b = lw3 b (X2 ∷ CK20 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn01547 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01547 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl
wn01548 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01548 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl
wn01549 : Base 3 → ⟪ (K2⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ K2⁻ ∷ []) ⟫ʷ
wn01549 b = lw0 b (K2⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ K2⁻ ∷ []) tt tt Eq.refl
wn01550 : Base 3 → ⟪ (K2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ K2 ∷ []) ⟫ʷ
wn01550 b = lw0 b (K2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ K2 ∷ []) tt tt Eq.refl
wn01551 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01551 b = lw0 b (X2 ∷ CS12⁻ ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) tt tt Eq.refl
wn01552 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01552 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn01553 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01553 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn01554 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01554 b = lw0 b (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01555 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01555 b = lw0 b (X2 ∷ CK21⁻ ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn01556 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01556 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl
wn01557 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01557 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl
wn01558 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01558 b = lw0 b (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01559 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01559 b = lw0 b (X2 ∷ CK21 ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01560 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01560 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01561 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01561 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01562 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01562 b = lw0 b (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) tt tt Eq.refl
wn01563 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01563 b = lw0 b (X2 ∷ CS12 ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01564 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01564 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01565 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01565 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01566 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01566 b = lw0 b (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn01567 : Base 3 → ⟪ (X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01567 b = lw3 b (X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01568 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ
wn01568 b = lw3 b (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ []) tt tt Eq.refl
wn01569 : Base 3 → ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
wn01569 b = lw3 b (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) tt tt Eq.refl
wn01570 : Base 3 → ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ []) ⟫ʷ
wn01570 b = lw3 b (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ []) tt tt Eq.refl
wn01571 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ CK21⁻ ∷ []) ⟫ʷ
wn01571 b = lw0 b (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ CK21⁻ ∷ []) tt tt Eq.refl
wn01572 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ
wn01572 b = lw0 b (X3 ∷ CS13 ∷ X3 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ CK21⁻ ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) tt tt Eq.refl
wn01573 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS12 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ
wn01573 b = lw0 b (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ CS12 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn01574 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS12 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ
wn01574 b = lw0 b (X3 ∷ CK31 ∷ X3 ∷ CS12 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ CS12⁻ ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) tt tt Eq.refl
wn01575 : Base 3 → ⟪ (X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn01575 b = lw0 b (X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn01576 : Base 3 → ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ
wn01576 b = lw0 b (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ []) tt tt Eq.refl
wn01577 : Base 3 → ⟪ (X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CZ12 ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn01577 b = lw0 b (X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ CZ12 ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn01578 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ CZ12 ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ
wn01578 b = lw0 b (X3 ∷ CK31 ∷ X3 ∷ CZ12 ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ []) tt tt Eq.refl
wn01579 : Base 3 → ⟪ (X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ X3 ∷ CK12 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ CK12⁻ ∷ []) ⟫ʷ
wn01579 b = lw0 b (X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ CK12 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ CK12⁻ ∷ []) tt tt Eq.refl

------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL04 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl0636 : Complete 4 → ⟪ (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CZ34 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0636 c4 = lw0 c4 (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CZ34 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl

wl0637 : Complete 4 → ⟪ (CCZ134 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ124 ∷ CCZ134 ∷ []) ⟫ʷ
wl0637 c4 = lw0 c4 (CCZ134 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0638 : Complete 4 → ⟪ (K0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0638 c4 = lw4 c4 (K0 ∷ K0⁻ ∷ []) [] tt tt Eq.refl

wl0639 : Complete 4 → ⟪ (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0639 c4 = lw0 c4 (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) [] tt tt Eq.refl

wl0640 : Complete 4 → ⟪ (CS24 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS24 ∷ []) ⟫ʷ
wl0640 c4 = lw1 c4 (CS24 ∷ S0 ∷ []) (S0 ∷ CS24 ∷ []) tt tt Eq.refl

wl0641 : Complete 4 → ⟪ (CS24⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0641 c4 = lw1 c4 (CS24⁻ ∷ S0 ∷ []) (S0 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0642 : Complete 4 → ⟪ (S1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S2 ∷ []) ⟫ʷ
wl0642 c4 = lw4 c4 (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) tt tt Eq.refl

wl0643 : Complete 4 → ⟪ (S2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S1 ∷ []) ⟫ʷ
wl0643 c4 = lw4 c4 (S2 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ []) tt tt Eq.refl

wl0644 : Complete 4 → ⟪ (S2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ S3 ∷ []) ⟫ʷ
wl0644 c4 = lw4 c4 (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ []) tt tt Eq.refl

wl0645 : Complete 4 → ⟪ (S3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ S2 ∷ []) ⟫ʷ
wl0645 c4 = lw4 c4 (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) tt tt Eq.refl

wl0646 : Complete 4 → ⟪ (S3 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ S4 ∷ []) ⟫ʷ
wl0646 c4 = lw0 c4 (S3 ∷ Sw34 ∷ []) (Sw34 ∷ S4 ∷ []) tt tt Eq.refl

wl0647 : Complete 4 → ⟪ (S4 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ S3 ∷ []) ⟫ʷ
wl0647 c4 = lw0 c4 (S4 ∷ Sw34 ∷ []) (Sw34 ∷ S3 ∷ []) tt tt Eq.refl

wl0648 : Complete 4 → ⟪ (CK01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK10 ∷ []) ⟫ʷ
wl0648 c4 = lw4 c4 (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) tt tt Eq.refl

wl0649 : Complete 4 → ⟪ (CK10 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK01 ∷ []) ⟫ʷ
wl0649 c4 = lw4 c4 (CK10 ∷ Sw01 ∷ []) (Sw01 ∷ CK01 ∷ []) tt tt Eq.refl

wl0650 : Complete 4 → ⟪ (CK01 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CK01 ∷ []) ⟫ʷ
wl0650 c4 = lw4 c4 (CK01 ∷ CS23 ∷ []) (CS23 ∷ CK01 ∷ []) tt tt Eq.refl

wl0651 : Complete 4 → ⟪ (CK01 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CK01 ∷ []) ⟫ʷ
wl0651 c4 = lw4 c4 (CK01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK01 ∷ []) tt tt Eq.refl

wl0652 : Complete 4 → ⟪ (CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
wl0652 c4 = lw4 c4 (CS12⁻ ∷ []) (CS12⁻ ∷ []) tt tt Eq.refl

wl0653 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) ⟫ʷ
wl0653 c4 = lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) tt tt Eq.refl

wl0654 : Complete 4 → ⟪ (CS14⁻ ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0654 c4 = lw0 c4 (CS14⁻ ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0655 : Complete 4 → ⟪ (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14 ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) ⟫ʷ
wl0655 c4 = lw0 c4 (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) tt tt Eq.refl

wl0656 : Complete 4 → ⟪ (CX43 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0656 c4 = lw0 c4 (CX43 ∷ CX43 ∷ []) [] tt tt Eq.refl

wl0657 : Complete 4 → ⟪ (CCZ124 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ124 ∷ []) ⟫ʷ
wl0657 c4 = lw0 c4 (CCZ124 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0658 : Complete 4 → ⟪ (CCZ124 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CS13⁻ ∷ CX43 ∷ CCZ124 ∷ []) ⟫ʷ
wl0658 c4 = lw0 c4 (CCZ124 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (CX43 ∷ CS13⁻ ∷ CX43 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0659 : Complete 4 → ⟪ (CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0659 c4 = lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl

wl0660 : Complete 4 → ⟪ (Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ []) ⟫ʷ
wl0660 c4 = lw0 c4 (Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0661 : Complete 4 → ⟪ (CCZ123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ123 ∷ []) ⟫ʷ
wl0661 c4 = lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0662 : Complete 4 → ⟪ (CCZ123 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CCZ123 ∷ []) ⟫ʷ
wl0662 c4 = lw0 c4 (CCZ123 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0663 : Complete 4 → ⟪ (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ []) ⟫ʷ
wl0663 c4 = lw0 c4 (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wl0664 : Complete 4 → ⟪ (CS13 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS13 ∷ []) ⟫ʷ
wl0664 c4 = lw0 c4 (CS13 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS13 ∷ []) tt tt Eq.refl

wl0665 : Complete 4 → ⟪ (CS13⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0665 c4 = lw0 c4 (CS13⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0666 : Complete 4 → ⟪ (Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ Toff134 ∷ []) ⟫ʷ
wl0666 c4 = lw0 c4 (Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff134 ∷ []) tt tt Eq.refl

wl0667 : Complete 4 → ⟪ (CS12 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS12 ∷ []) ⟫ʷ
wl0667 c4 = lw0 c4 (CS12 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS12 ∷ []) tt tt Eq.refl

wl0668 : Complete 4 → ⟪ (CS12⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0668 c4 = lw0 c4 (CS12⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0669 : Complete 4 → ⟪ (Toff314 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ []) ⟫ʷ
wl0669 c4 = lw0 c4 (Toff314 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0670 : Complete 4 → ⟪ (CCZ123 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CCZ123 ∷ []) ⟫ʷ
wl0670 c4 = lw0 c4 (CCZ123 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0671 : Complete 4 → ⟪ (Toff324 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ Toff324 ∷ []) ⟫ʷ
wl0671 c4 = lw0 c4 (Toff324 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wl0672 : Complete 4 → ⟪ (CS13 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS13 ∷ []) ⟫ʷ
wl0672 c4 = lw0 c4 (CS13 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS13 ∷ []) tt tt Eq.refl

wl0673 : Complete 4 → ⟪ (CS13⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0673 c4 = lw0 c4 (CS13⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0674 : Complete 4 → ⟪ (Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ []) ⟫ʷ
wl0674 c4 = lw0 c4 (Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ []) tt tt Eq.refl

wl0675 : Complete 4 → ⟪ (CS12 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS12 ∷ []) ⟫ʷ
wl0675 c4 = lw0 c4 (CS12 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS12 ∷ []) tt tt Eq.refl

wl0676 : Complete 4 → ⟪ (CS12⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0676 c4 = lw0 c4 (CS12⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0677 : Complete 4 → ⟪ (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ []) ⟫ʷ
wl0677 c4 = lw0 c4 (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0678 : Complete 4 → ⟪ (CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ []) ⟫ʷ
wl0678 c4 = lw0 c4 (CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0679 : Complete 4 → ⟪ (Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ []) ⟫ʷ
wl0679 c4 = lw0 c4 (Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wl0680 : Complete 4 → ⟪ (CS13 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS13 ∷ []) ⟫ʷ
wl0680 c4 = lw0 c4 (CS13 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS13 ∷ []) tt tt Eq.refl

wl0681 : Complete 4 → ⟪ (CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0681 c4 = lw0 c4 (CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0682 : Complete 4 → ⟪ (Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ []) ⟫ʷ
wl0682 c4 = lw0 c4 (Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ []) tt tt Eq.refl

wl0683 : Complete 4 → ⟪ (CS12 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS12 ∷ []) ⟫ʷ
wl0683 c4 = lw0 c4 (CS12 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS12 ∷ []) tt tt Eq.refl

wl0684 : Complete 4 → ⟪ (CS12⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0684 c4 = lw0 c4 (CS12⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0685 : Complete 4 → ⟪ (Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ []) ⟫ʷ
wl0685 c4 = lw0 c4 (Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0686 : Complete 4 → ⟪ (CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ []) ⟫ʷ
wl0686 c4 = lw0 c4 (CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0687 : Complete 4 → ⟪ (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ []) ⟫ʷ
wl0687 c4 = lw0 c4 (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wl0688 : Complete 4 → ⟪ (CS13 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS13 ∷ []) ⟫ʷ
wl0688 c4 = lw0 c4 (CS13 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS13 ∷ []) tt tt Eq.refl

wl0689 : Complete 4 → ⟪ (CS13⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0689 c4 = lw0 c4 (CS13⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0690 : Complete 4 → ⟪ (Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ []) ⟫ʷ
wl0690 c4 = lw0 c4 (Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ []) tt tt Eq.refl

wl0691 : Complete 4 → ⟪ (CS12 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ []) ⟫ʷ
wl0691 c4 = lw0 c4 (CS12 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ []) tt tt Eq.refl

wl0692 : Complete 4 → ⟪ (CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0692 c4 = lw0 c4 (CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0693 : Complete 4 → ⟪ (CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CCZ124 ∷ []) ⟫ʷ
wl0693 c4 = lw0 c4 (CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0694 : Complete 4 → ⟪ (Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ Toff314 ∷ []) ⟫ʷ
wl0694 c4 = lw0 c4 (Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0695 : Complete 4 → ⟪ (Toff324 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ Toff324 ∷ []) ⟫ʷ
wl0695 c4 = lw0 c4 (Toff324 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wl0696 : Complete 4 → ⟪ (CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0696 c4 = lw0 c4 (CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0697 : Complete 4 → ⟪ (Toff134 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ Toff134 ∷ []) ⟫ʷ
wl0697 c4 = lw0 c4 (Toff134 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff134 ∷ []) tt tt Eq.refl

wl0698 : Complete 4 → ⟪ (CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0698 c4 = lw0 c4 (CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0699 : Complete 4 → ⟪ (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ Toff314 ∷ []) ⟫ʷ
wl0699 c4 = lw0 c4 (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0700 : Complete 4 → ⟪ (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ Toff324 ∷ []) ⟫ʷ
wl0700 c4 = lw0 c4 (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wl0701 : Complete 4 → ⟪ (CS13 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS13 ∷ []) ⟫ʷ
wl0701 c4 = lw0 c4 (CS13 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS13 ∷ []) tt tt Eq.refl

wl0702 : Complete 4 → ⟪ (CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0702 c4 = lw0 c4 (CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0703 : Complete 4 → ⟪ (Toff134 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ Toff134 ∷ []) ⟫ʷ
wl0703 c4 = lw0 c4 (Toff134 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff134 ∷ []) tt tt Eq.refl

wl0704 : Complete 4 → ⟪ (CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0704 c4 = lw0 c4 (CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0705 : Complete 4 → ⟪ (CCZ234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CCZ234 ∷ []) ⟫ʷ
wl0705 c4 = lw0 c4 (CCZ234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0706 : Complete 4 → ⟪ (Toff314 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ Toff314 ∷ []) ⟫ʷ
wl0706 c4 = lw0 c4 (Toff314 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0707 : Complete 4 → ⟪ (Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ Toff324 ∷ []) ⟫ʷ
wl0707 c4 = lw0 c4 (Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wl0708 : Complete 4 → ⟪ (CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0708 c4 = lw0 c4 (CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0709 : Complete 4 → ⟪ (Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ Toff134 ∷ []) ⟫ʷ
wl0709 c4 = lw0 c4 (Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff134 ∷ []) tt tt Eq.refl

wl0710 : Complete 4 → ⟪ (CS12 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS12 ∷ []) ⟫ʷ
wl0710 c4 = lw0 c4 (CS12 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS12 ∷ []) tt tt Eq.refl

wl0711 : Complete 4 → ⟪ (CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0711 c4 = lw0 c4 (CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0712 : Complete 4 → ⟪ (S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0712 c4 = lw0 c4 (S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0713 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ123 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0713 c4 = lw0 c4 (S4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0714 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0714 c4 = lw0 c4 (CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0715 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0715 c4 = lw0 c4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0716 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0716 c4 = lw0 c4 (CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0717 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0717 c4 = lw0 c4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0718 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0718 c4 = lw0 c4 (CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0719 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0719 c4 = lw0 c4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0720 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wl0720 c4 = lw0 c4 (S4⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0721 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wl0721 c4 = lw0 c4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0722 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) ⟫ʷ
wl0722 c4 = lw0 c4 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) tt tt Eq.refl

wl0723 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) ⟫ʷ
wl0723 c4 = lw0 c4 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) tt tt Eq.refl

wl0724 : Complete 4 → ⟪ (K1 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ K1 ∷ []) ⟫ʷ
wl0724 c4 = lw4 c4 (K1 ∷ Toff203 ∷ []) (Toff203 ∷ K1 ∷ []) tt tt Eq.refl

wl0725 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0725 c4 = lw0 c4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (X4 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0726 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0726 c4 = lw0 c4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0727 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0727 c4 = lw0 c4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0728 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K2 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0728 c4 = lw0 c4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0729 : Complete 4 → ⟪ (CK42 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) ⟫ʷ
wl0729 c4 = lw1 c4 (CK42 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) tt tt Eq.refl

wl0730 : Complete 4 → ⟪ (K2 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K2 ∷ []) ⟫ʷ
wl0730 c4 = lw0 c4 (K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ []) tt tt Eq.refl

wl0731 : Complete 4 → ⟪ (CK43 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) ⟫ʷ
wl0731 c4 = lw1 c4 (CK43 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) tt tt Eq.refl

wl0732 : Complete 4 → ⟪ (K3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K3 ∷ []) ⟫ʷ
wl0732 c4 = lw0 c4 (K3 ∷ X4 ∷ []) (X4 ∷ K3 ∷ []) tt tt Eq.refl

wl0733 : Complete 4 → ⟪ (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ []) ⟫ʷ
wl0733 c4 = lw0 c4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ []) tt tt Eq.refl

wl0734 : Complete 4 → ⟪ (CCZ123 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ123 ∷ []) ⟫ʷ
wl0734 c4 = lw4 c4 (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0735 : Complete 4 → ⟪ (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ X4 ∷ CCZ234 ∷ []) ⟫ʷ
wl0735 c4 = lw0 c4 (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0736 : Complete 4 → ⟪ (CS23 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS23 ∷ []) ⟫ʷ
wl0736 c4 = lw0 c4 (CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ []) tt tt Eq.refl

wl0737 : Complete 4 → ⟪ (CX42 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CZ24 ∷ K2⁻ ∷ []) ⟫ʷ
wl0737 c4 = lw0 c4 (CX42 ∷ []) (K2 ∷ CZ24 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0738 : Complete 4 → ⟪ (K2⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K2⁻ ∷ []) ⟫ʷ
wl0738 c4 = lw0 c4 (K2⁻ ∷ X4 ∷ []) (X4 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0739 : Complete 4 → ⟪ (CS23⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS23⁻ ∷ []) ⟫ʷ
wl0739 c4 = lw0 c4 (CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ []) tt tt Eq.refl

wl0740 : Complete 4 → ⟪ (K3⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K3⁻ ∷ []) ⟫ʷ
wl0740 c4 = lw0 c4 (K3⁻ ∷ X4 ∷ []) (X4 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0741 : Complete 4 → ⟪ (CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ []) ⟫ʷ
wl0741 c4 = lw0 c4 (CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ []) tt tt Eq.refl

wl0742 : Complete 4 → ⟪ (CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0742 c4 = lw0 c4 (CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0743 : Complete 4 → ⟪ (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ []) ⟫ʷ
wl0743 c4 = lw0 c4 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl

wl0744 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) ⟫ʷ
wl0744 c4 = lw0 c4 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0745 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) ⟫ʷ
wl0745 c4 = lw0 c4 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0746 : Complete 4 → ⟪ (K1⁻ ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ K1⁻ ∷ []) ⟫ʷ
wl0746 c4 = lw4 c4 (K1⁻ ∷ Toff203 ∷ []) (Toff203 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0747 : Complete 4 → ⟪ (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) ⟫ʷ
wl0747 c4 = lw0 c4 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0748 : Complete 4 → ⟪ (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) ⟫ʷ
wl0748 c4 = lw0 c4 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0749 : Complete 4 → ⟪ (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0749 c4 = lw0 c4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0750 : Complete 4 → ⟪ (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0750 c4 = lw0 c4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0751 : Complete 4 → ⟪ (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0751 c4 = lw0 c4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0752 : Complete 4 → ⟪ (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0752 c4 = lw0 c4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0753 : Complete 4 → ⟪ (CS13 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS13 ∷ []) ⟫ʷ
wl0753 c4 = lw4 c4 (CS13 ∷ Toff203 ∷ []) (Toff203 ∷ CS13 ∷ []) tt tt Eq.refl

wl0754 : Complete 4 → ⟪ (CS12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ []) ⟫ʷ
wl0754 c4 = lw0 c4 (CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ []) tt tt Eq.refl

wl0755 : Complete 4 → ⟪ (CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0755 c4 = lw0 c4 (CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0756 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13⁻ ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0756 c4 = lw0 c4 (S4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0757 : Complete 4 → ⟪ (S4 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0757 c4 = lw0 c4 (S4 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0758 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0758 c4 = lw0 c4 (S4 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0759 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13⁻ ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0759 c4 = lw0 c4 (CS14 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0760 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0760 c4 = lw0 c4 (CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0761 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0761 c4 = lw0 c4 (CS14 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0762 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0762 c4 = lw0 c4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0763 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0763 c4 = lw0 c4 (CS24 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0764 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0764 c4 = lw0 c4 (CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0765 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0765 c4 = lw0 c4 (CS24 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0766 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0766 c4 = lw0 c4 (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0767 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0767 c4 = lw0 c4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0768 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0768 c4 = lw0 c4 (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0769 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13⁻ ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wl0769 c4 = lw0 c4 (S4⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0770 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wl0770 c4 = lw0 c4 (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0771 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wl0771 c4 = lw0 c4 (S4⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0772 : Complete 4 → ⟪ (K0 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K0 ∷ []) ⟫ʷ
wl0772 c4 = lw1 c4 (K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ []) tt tt Eq.refl

wl0773 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) ⟫ʷ
wl0773 c4 = lw0 c4 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) tt tt Eq.refl

wl0774 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) ⟫ʷ
wl0774 c4 = lw0 c4 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) tt tt Eq.refl

wl0775 : Complete 4 → ⟪ (CCZ023 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CCZ023 ∷ []) ⟫ʷ
wl0775 c4 = lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0776 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) ⟫ʷ
wl0776 c4 = lw0 c4 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) tt tt Eq.refl

wl0777 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) ⟫ʷ
wl0777 c4 = lw0 c4 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) tt tt Eq.refl

wl0778 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) ⟫ʷ
wl0778 c4 = lw0 c4 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) tt tt Eq.refl

wl0779 : Complete 4 → ⟪ (K2 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ K2 ∷ []) ⟫ʷ
wl0779 c4 = lw4 c4 (K2 ∷ Toff013 ∷ []) (Toff013 ∷ K2 ∷ []) tt tt Eq.refl

wl0780 : Complete 4 → ⟪ (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ []) ⟫ʷ
wl0780 c4 = lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl

wl0781 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0781 c4 = lw1 c4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0782 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0782 c4 = lw0 c4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0783 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K0 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0783 c4 = lw1 c4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0784 : Complete 4 → ⟪ (Toff412 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0784 c4 = lw0 c4 (Toff412 ∷ Toff412 ∷ []) [] tt tt Eq.refl

wl0785 : Complete 4 → ⟪ (Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ []) ⟫ʷ
wl0785 c4 = lw0 c4 (Toff412 ∷ []) (Toff412 ∷ []) tt tt Eq.refl

wl0786 : Complete 4 → ⟪ (CCZ123 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ123 ∷ []) ⟫ʷ
wl0786 c4 = lw0 c4 (CCZ123 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0787 : Complete 4 → ⟪ (CCZ012 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ012 ∷ []) ⟫ʷ
wl0787 c4 = lw3 c4 (CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ []) tt tt Eq.refl

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

module Examples.Groups.Clifford+CS.Four.Wins.W20 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)

wn00995 : Base 3 → ⟪ (CS23⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00995 b = lw0 b (CS23⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CS23⁻ ∷ []) tt tt Eq.refl
wn00996 : Base 3 → ⟪ (CS23 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS23 ∷ []) ⟫ʷ
wn00996 b = lw0 b (CS23 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CS23 ∷ []) tt tt Eq.refl
wn00997 : Base 3 → ⟪ (CS12 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
wn00997 b = lw3 b (CS12 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ CS12 ∷ []) tt tt Eq.refl
wn00998 : Base 3 → ⟪ (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn00998 b = lw0 b (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl
wn00999 : Base 3 → ⟪ (CS23⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00999 b = lw0 b (CS23⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ CS23⁻ ∷ []) tt tt Eq.refl
wn01000 : Base 3 → ⟪ (CS12 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
wn01000 b = lw3 b (CS12 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ CS12 ∷ []) tt tt Eq.refl
wn01001 : Base 3 → ⟪ (CS23⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS23⁻ ∷ []) ⟫ʷ
wn01001 b = lw0 b (CS23⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CS23⁻ ∷ []) tt tt Eq.refl
wn01002 : Base 3 → ⟪ (CS12 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
wn01002 b = lw3 b (CS12 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ CS12 ∷ []) tt tt Eq.refl
wn01003 : Base 3 → ⟪ (CS23⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS23⁻ ∷ []) ⟫ʷ
wn01003 b = lw0 b (CS23⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS23⁻ ∷ []) tt tt Eq.refl
wn01004 : Base 3 → ⟪ (CS23 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS23 ∷ []) ⟫ʷ
wn01004 b = lw0 b (CS23 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS23 ∷ []) tt tt Eq.refl
wn01005 : Base 3 → ⟪ (CS12 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
wn01005 b = lw3 b (CS12 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ CS12 ∷ []) tt tt Eq.refl
wn01006 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
wn01006 b = lw0 b (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) tt tt Eq.refl
wn01007 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
wn01007 b = lw0 b (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) tt tt Eq.refl
wn01008 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
wn01008 b = lw3 b (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) tt tt Eq.refl
wn01009 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
wn01009 b = lw3 b (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) tt tt Eq.refl
wn01010 : Base 3 → ⟪ (CCZ123 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
wn01010 b = lw0 b (CCZ123 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01011 : Base 3 → ⟪ (CCZ123 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
wn01011 b = lw0 b (CCZ123 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01012 : Base 3 → ⟪ (CZ12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CZ12 ∷ []) ⟫ʷ
wn01012 b = lw0 b (CZ12 ∷ CS13 ∷ []) (CS13 ∷ CZ12 ∷ []) tt tt Eq.refl
wn01013 : Base 3 → ⟪ (CZ12 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CZ12 ∷ []) ⟫ʷ
wn01013 b = lw0 b (CZ12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ12 ∷ []) tt tt Eq.refl
wn01014 : Base 3 → ⟪ (CCZ123 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
wn01014 b = lw0 b (CCZ123 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01015 : Base 3 → ⟪ (CCZ123 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
wn01015 b = lw0 b (CCZ123 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01016 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
wn01016 b = lw3 b (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) tt tt Eq.refl
wn01017 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
wn01017 b = lw3 b (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) tt tt Eq.refl
wn01018 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
wn01018 b = lw0 b [] (X2 ∷ X3 ∷ X2 ∷ X3 ∷ []) tt tt Eq.refl
wn01019 : Base 3 → ⟪ (X2 ∷ CS23 ∷ X2 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
wn01019 b = lw0 b (X2 ∷ CS23 ∷ X2 ∷ Toff123 ∷ []) (Toff123 ∷ X2 ∷ CS23 ∷ X2 ∷ []) tt tt Eq.refl
wn01020 : Base 3 → ⟪ (X2 ∷ CK23 ∷ X2 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
wn01020 b = lw0 b (X2 ∷ CK23 ∷ X2 ∷ Toff123 ∷ []) (Toff123 ∷ X2 ∷ CK23 ∷ X2 ∷ []) tt tt Eq.refl
wn01021 : Base 3 → ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
wn01021 b = lw0 b (X2 ∷ CS23⁻ ∷ X2 ∷ Toff123 ∷ []) (Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01022 : Base 3 → ⟪ (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
wn01022 b = lw0 b (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01023 : Base 3 → ⟪ (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
wn01023 b = lw0 b (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01024 : Base 3 → ⟪ (CZ13 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CZ13 ∷ []) ⟫ʷ
wn01024 b = lw0 b (CZ13 ∷ CS13 ∷ []) (CS13 ∷ CZ13 ∷ []) tt tt Eq.refl
wn01025 : Base 3 → ⟪ (Z1 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Z1 ∷ []) ⟫ʷ
wn01025 b = lw0 b (Z1 ∷ CS13 ∷ []) (CS13 ∷ Z1 ∷ []) tt tt Eq.refl
wn01026 : Base 3 → ⟪ (CZ13 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CZ13 ∷ []) ⟫ʷ
wn01026 b = lw0 b (CZ13 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ13 ∷ []) tt tt Eq.refl
wn01027 : Base 3 → ⟪ (Z1 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Z1 ∷ []) ⟫ʷ
wn01027 b = lw0 b (Z1 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Z1 ∷ []) tt tt Eq.refl
wn01028 : Base 3 → ⟪ (CCZ123 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
wn01028 b = lw0 b (CCZ123 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01029 : Base 3 → ⟪ (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
wn01029 b = lw0 b (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01030 : Base 3 → ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
wn01030 b = lw0 b (X2 ∷ CK23⁻ ∷ X2 ∷ Toff123 ∷ []) (Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01031 : Base 3 → ⟪ (CX12 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ CX12 ∷ []) ⟫ʷ
wn01031 b = lw0 b (CX12 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CX12 ∷ []) tt tt Eq.refl
wn01032 : Base 3 → ⟪ (CK10 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ CK10 ∷ []) ⟫ʷ
wn01032 b = lw3 b (CK10 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CK10 ∷ []) tt tt Eq.refl
wn01033 : Base 3 → ⟪ (CS01 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS01 ∷ []) ⟫ʷ
wn01033 b = lw3 b (CS01 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CS01 ∷ []) tt tt Eq.refl
wn01034 : Base 3 → ⟪ (CX12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CX12 ∷ []) ⟫ʷ
wn01034 b = lw0 b (CX12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CX12 ∷ []) tt tt Eq.refl
wn01035 : Base 3 → ⟪ (CK10 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CK10 ∷ []) ⟫ʷ
wn01035 b = lw3 b (CK10 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CK10 ∷ []) tt tt Eq.refl
wn01036 : Base 3 → ⟪ (CS01 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01 ∷ []) ⟫ʷ
wn01036 b = lw3 b (CS01 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01 ∷ []) tt tt Eq.refl
wn01037 : Base 3 → ⟪ (CCZ123 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
wn01037 b = lw0 b (CCZ123 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01038 : Base 3 → ⟪ (CCZ123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
wn01038 b = lw0 b (CCZ123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ X3 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01039 : Base 3 → ⟪ (CCZ123 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
wn01039 b = lw0 b (CCZ123 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01040 : Base 3 → ⟪ (CZ12 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CZ12 ∷ []) ⟫ʷ
wn01040 b = lw0 b (CZ12 ∷ CS23 ∷ []) (CS23 ∷ CZ12 ∷ []) tt tt Eq.refl
wn01041 : Base 3 → ⟪ (CZ12 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CZ12 ∷ []) ⟫ʷ
wn01041 b = lw0 b (CZ12 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CZ12 ∷ []) tt tt Eq.refl
wn01042 : Base 3 → ⟪ (CCZ123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
wn01042 b = lw0 b (CCZ123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01043 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn01043 b = lw0 b (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) tt tt Eq.refl
wn01044 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn01044 b = lw0 b (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) tt tt Eq.refl
wn01045 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn01045 b = lw3 b (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn01046 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn01046 b = lw3 b (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn01047 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn01047 b = lw3 b (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn01048 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn01048 b = lw3 b (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn01049 : Base 3 → ⟪ (X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ []) ⟫ʷ
wn01049 b = lw3 b (X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ []) tt tt Eq.refl
wn01050 : Base 3 → ⟪ (X1 ∷ CS12 ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CS12 ∷ X1 ∷ []) ⟫ʷ
wn01050 b = lw3 b (X1 ∷ CS12 ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CS12 ∷ X1 ∷ []) tt tt Eq.refl
wn01051 : Base 3 → ⟪ (X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ []) ⟫ʷ
wn01051 b = lw3 b (X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn01052 : Base 3 → ⟪ (CK13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK23 ∷ []) ⟫ʷ
wn01052 b = lw0 b (CK13 ∷ Sw12 ∷ []) (Sw12 ∷ CK23 ∷ []) tt tt Eq.refl
wn01053 : Base 3 → ⟪ (CK23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK13 ∷ []) ⟫ʷ
wn01053 b = lw0 b (CK23 ∷ Sw12 ∷ []) (Sw12 ∷ CK13 ∷ []) tt tt Eq.refl
wn01054 : Base 3 → ⟪ (X1 ∷ CK12 ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CK12 ∷ X1 ∷ []) ⟫ʷ
wn01054 b = lw3 b (X1 ∷ CK12 ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CK12 ∷ X1 ∷ []) tt tt Eq.refl
wn01055 : Base 3 → ⟪ (X1 ∷ CS12⁻ ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ []) ⟫ʷ
wn01055 b = lw3 b (X1 ∷ CS12⁻ ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn01056 : Base 3 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) ⟫ʷ
wn01056 b = lw0 b (CCZ123 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) tt tt Eq.refl
wn01057 : Base 3 → ⟪ (CS12⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS12⁻ ∷ []) ⟫ʷ
wn01057 b = lw3 b (CS12⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn01058 : Base 3 → ⟪ (CS12 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS12 ∷ []) ⟫ʷ
wn01058 b = lw3 b (CS12 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS12 ∷ []) tt tt Eq.refl
wn01059 : Base 3 → ⟪ (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn01059 b = lw0 b (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl
wn01060 : Base 3 → ⟪ (CS12⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CS12⁻ ∷ []) ⟫ʷ
wn01060 b = lw3 b (CS12⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn01061 : Base 3 → ⟪ (CS12 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CS12 ∷ []) ⟫ʷ
wn01061 b = lw3 b (CS12 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS12 ∷ []) tt tt Eq.refl
wn01062 : Base 3 → ⟪ (CS02 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS02 ∷ []) ⟫ʷ
wn01062 b = lw3 b (CS02 ∷ ι ∷ []) (ι ∷ CS02 ∷ []) tt tt Eq.refl
wn01063 : Base 3 → ⟪ (CS02 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CS02 ∷ []) ⟫ʷ
wn01063 b = lw3 b (CS02 ∷ Z1 ∷ []) (Z1 ∷ CS02 ∷ []) tt tt Eq.refl
wn01064 : Base 3 → ⟪ (CS13 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ CS13 ∷ []) ⟫ʷ
wn01064 b = lw0 b (CS13 ∷ Z2 ∷ []) (Z2 ∷ CS13 ∷ []) tt tt Eq.refl
wn01065 : Base 3 → ⟪ (Z3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Z2 ∷ []) ⟫ʷ
wn01065 b = lw0 b (Z3 ∷ Sw23 ∷ []) (Sw23 ∷ Z2 ∷ []) tt tt Eq.refl
wn01066 : Base 3 → ⟪ (CS02 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ CS02 ∷ []) ⟫ʷ
wn01066 b = lw3 b (CS02 ∷ Z2 ∷ []) (Z2 ∷ CS02 ∷ []) tt tt Eq.refl
wn01067 : Base 3 → ⟪ (Toff012 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff012 ∷ []) ⟫ʷ
wn01067 b = lw3 b (Toff012 ∷ ι ∷ []) (ι ∷ Toff012 ∷ []) tt tt Eq.refl
wn01068 : Base 3 → ⟪ (Toff012 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ Toff012 ∷ []) ⟫ʷ
wn01068 b = lw3 b (Toff012 ∷ Z1 ∷ []) (Z1 ∷ Toff012 ∷ []) tt tt Eq.refl
wn01069 : Base 3 → ⟪ (Toff012 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ Toff012 ∷ []) ⟫ʷ
wn01069 b = lw3 b (Toff012 ∷ Z2 ∷ []) (Z2 ∷ Toff012 ∷ []) tt tt Eq.refl
wn01070 : Base 3 → ⟪ (Toff012 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Toff012 ∷ []) ⟫ʷ
wn01070 b = lw3 b (Toff012 ∷ CZ12 ∷ []) (CZ12 ∷ Toff012 ∷ []) tt tt Eq.refl
wn01071 : Base 3 → ⟪ (CS02⁻ ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS02⁻ ∷ []) ⟫ʷ
wn01071 b = lw3 b (CS02⁻ ∷ ι ∷ []) (ι ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn01072 : Base 3 → ⟪ (CS02⁻ ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CS02⁻ ∷ []) ⟫ʷ
wn01072 b = lw3 b (CS02⁻ ∷ Z1 ∷ []) (Z1 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn01073 : Base 3 → ⟪ (CS13⁻ ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ CS13⁻ ∷ []) ⟫ʷ
wn01073 b = lw0 b (CS13⁻ ∷ Z2 ∷ []) (Z2 ∷ CS13⁻ ∷ []) tt tt Eq.refl
wn01074 : Base 3 → ⟪ (CS02⁻ ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn01074 b = lw3 b (CS02⁻ ∷ Z2 ∷ []) (Z2 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn01075 : Base 3 → ⟪ (CS13⁻ ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CS13⁻ ∷ []) ⟫ʷ
wn01075 b = lw0 b (CS13⁻ ∷ CZ23 ∷ []) (CZ23 ∷ CS13⁻ ∷ []) tt tt Eq.refl
wn01076 : Base 3 → ⟪ (CS12⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ CS12⁻ ∷ []) ⟫ʷ
wn01076 b = lw3 b (CS12⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn01077 : Base 3 → ⟪ (CS12 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ CS12 ∷ []) ⟫ʷ
wn01077 b = lw3 b (CS12 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CS12 ∷ []) tt tt Eq.refl
wn01078 : Base 3 → ⟪ (CS12⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS12⁻ ∷ []) ⟫ʷ
wn01078 b = lw3 b (CS12⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn01079 : Base 3 → ⟪ (CS12 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS12 ∷ []) ⟫ʷ
wn01079 b = lw3 b (CS12 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS12 ∷ []) tt tt Eq.refl
wn01080 : Base 3 → ⟪ (CK13⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK23⁻ ∷ []) ⟫ʷ
wn01080 b = lw0 b (CK13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CK23⁻ ∷ []) tt tt Eq.refl
wn01081 : Base 3 → ⟪ (CK23⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK13⁻ ∷ []) ⟫ʷ
wn01081 b = lw0 b (CK23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CK13⁻ ∷ []) tt tt Eq.refl
wn01082 : Base 3 → ⟪ (X1 ∷ CK12⁻ ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) ⟫ʷ
wn01082 b = lw3 b (X1 ∷ CK12⁻ ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) tt tt Eq.refl

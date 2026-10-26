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

module Examples.Groups.Clifford+CS.Four.Wins.W28 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)

wn01421 : Base 3 → ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
wn01421 b = lw0 b (CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ []) (CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) tt tt Eq.refl
wn01422 : Base 3 → ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CK13⁻ ∷ []) ⟫ʷ
wn01422 b = lw0 b (Toff312 ∷ []) (CK13 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CK13⁻ ∷ []) tt tt Eq.refl
wn01423 : Base 3 → ⟪ (CK13 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CK13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wn01423 b = lw0 b (CK13 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CK13⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl
wn01424 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wn01424 b = lw3 b (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn01425 : Base 3 → ⟪ (CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn01425 b = lw3 b (CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) tt tt Eq.refl
wn01426 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
wn01426 b = lw3 b (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) tt tt Eq.refl
wn01427 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn01427 b = lw3 b (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) tt tt Eq.refl
wn01428 : Base 3 → ⟪ (CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ []) ⟫ʷ
wn01428 b = lw3 b (CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ []) tt tt Eq.refl
wn01429 : Base 3 → ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X0 ∷ CX02 ∷ X0 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX02 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn01429 b = lw3 b (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X0 ∷ []) (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X0 ∷ CX02 ∷ X0 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX02 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) tt tt Eq.refl
wn01430 : Base 3 → ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X0 ∷ CX02 ∷ X0 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX02 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X0 ∷ []) ⟫ʷ
wn01430 b = lw3 b (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X0 ∷ CX02 ∷ X0 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX02 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X0 ∷ []) tt tt Eq.refl
wn01431 : Base 3 → ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX01 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) ⟫ʷ
wn01431 b = lw3 b (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX01 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) tt tt Eq.refl
wn01432 : Base 3 → ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX01 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) ⟫ʷ
wn01432 b = lw3 b (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX01 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) tt tt Eq.refl
wn01433 : Base 3 → ⟪ (CX32 ∷ CS13 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
wn01433 b = lw0 b (CX32 ∷ CS13 ∷ CX32 ∷ []) (CS13 ∷ []) tt tt Eq.refl
wn01434 : Base 3 → ⟪ (CX32 ∷ CS13⁻ ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
wn01434 b = lw0 b (CX32 ∷ CS13⁻ ∷ CX32 ∷ []) (CS13⁻ ∷ []) tt tt Eq.refl
wn01435 : Base 3 → ⟪ (Toff012 ∷ CS02 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ012 ∷ CS02 ∷ []) ⟫ʷ
wn01435 b = lw3 b (Toff012 ∷ CS02 ∷ Toff012 ∷ []) (CS12 ∷ CCZ012 ∷ CS02 ∷ []) tt tt Eq.refl
wn01436 : Base 3 → ⟪ (CZ13 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01436 b = lw0 b (CZ13 ∷ CZ13 ∷ []) [] tt tt Eq.refl
wn01437 : Base 3 → ⟪ (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn01437 b = lw0 b (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) (Toff123 ∷ []) tt tt Eq.refl
wn01438 : Base 3 → ⟪ (CS12 ∷ CS12 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01438 b = lw3 b (CS12 ∷ CS12 ∷ CZ12 ∷ []) [] tt tt Eq.refl
wn01439 : Base 3 → ⟪ (CS02⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn01439 b = lw3 b (CS02⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01440 : Base 3 → ⟪ (CS12⁻ ∷ CS12⁻ ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01440 b = lw3 b (CS12⁻ ∷ CS12⁻ ∷ CZ12 ∷ []) [] tt tt Eq.refl
wn01441 : Base 3 → ⟪ (X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CZ01 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ
wn01441 b = lw3 b (X2 ∷ Toff012 ∷ X2 ∷ []) (K0 ∷ CZ01 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn01442 : Base 3 → ⟪ (K0 ∷ CZ01 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ
wn01442 b = lw3 b (K0 ∷ CZ01 ∷ CCZ012 ∷ K0⁻ ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ []) tt tt Eq.refl
wn01443 : Base 3 → ⟪ (S0 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn01443 b = lw3 b (S0 ∷ Toff012 ∷ []) (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01444 : Base 3 → ⟪ (CS13⁻ ∷ CS13⁻ ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01444 b = lw0 b (CS13⁻ ∷ CS13⁻ ∷ CZ13 ∷ []) [] tt tt Eq.refl
wn01445 : Base 3 → ⟪ (S0⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn01445 b = lw3 b (S0⁻ ∷ Toff012 ∷ []) (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01446 : Base 3 → ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Z0 ∷ CZ01 ∷ CZ02 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ
wn01446 b = lw3 b (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (K0 ∷ Z0 ∷ CZ01 ∷ CZ02 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn01447 : Base 3 → ⟪ (K0 ∷ Z0 ∷ CZ01 ∷ CZ02 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
wn01447 b = lw3 b (K0 ∷ Z0 ∷ CZ01 ∷ CZ02 ∷ CCZ012 ∷ K0⁻ ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) tt tt Eq.refl
wn01448 : Base 3 → ⟪ (K1⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ K1⁻ ∷ []) ⟫ʷ
wn01448 b = lw3 b (K1⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ K1⁻ ∷ []) tt tt Eq.refl
wn01449 : Base 3 → ⟪ (K1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ K1 ∷ []) ⟫ʷ
wn01449 b = lw3 b (K1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ K1 ∷ []) tt tt Eq.refl
wn01450 : Base 3 → ⟪ (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ []) ⟫ʷ
wn01450 b = lw3 b (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) tt tt Eq.refl
wn01451 : Base 3 → ⟪ (K1⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ K1⁻ ∷ []) ⟫ʷ
wn01451 b = lw3 b (K1⁻ ∷ CS02 ∷ []) (CS02 ∷ K1⁻ ∷ []) tt tt Eq.refl
wn01452 : Base 3 → ⟪ (K1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ K1 ∷ []) ⟫ʷ
wn01452 b = lw3 b (K1 ∷ CS02 ∷ []) (CS02 ∷ K1 ∷ []) tt tt Eq.refl
wn01453 : Base 3 → ⟪ (CZ12 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01453 b = lw3 b (CZ12 ∷ CZ12 ∷ []) [] tt tt Eq.refl
wn01454 : Base 3 → ⟪ (CS12 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
wn01454 b = lw3 b (CS12 ∷ CZ12 ∷ []) (CS12⁻ ∷ []) tt tt Eq.refl
wn01455 : Base 3 → ⟪ (CS12 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01455 b = lw3 b (CS12 ∷ CS12⁻ ∷ []) [] tt tt Eq.refl
wn01456 : Base 3 → ⟪ (CK20⁻ ∷ CS02 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS02 ∷ K0 ∷ []) ⟫ʷ
wn01456 b = lw3 b (CK20⁻ ∷ CS02 ∷ CK20 ∷ []) (K0⁻ ∷ CS02 ∷ K0 ∷ []) tt tt Eq.refl
wn01457 : Base 3 → ⟪ (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS02⁻ ∷ K0 ∷ []) ⟫ʷ
wn01457 b = lw3 b (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ []) (K0⁻ ∷ CS02⁻ ∷ K0 ∷ []) tt tt Eq.refl
wn01458 : Base 3 → ⟪ (Toff012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn01458 b = lw3 b (Toff012 ∷ K0⁻ ∷ []) (K0⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01459 : Base 3 → ⟪ (CK20 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01459 b = lw3 b (CK20 ∷ []) (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01460 : Base 3 → ⟪ (K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ []) ⟫ʷ
wn01460 b = lw3 b (K0 ∷ []) (K0 ∷ []) tt tt Eq.refl
wn01461 : Base 3 → ⟪ (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
wn01461 b = lw3 b (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (CK20 ∷ []) tt tt Eq.refl
wn01462 : Base 3 → ⟪ (CS02 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01462 b = lw3 b (CS02 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl
wn01463 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ []) ⟫ʷ
wn01463 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ []) tt tt Eq.refl
wn01464 : Base 3 → ⟪ (CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01464 b = lw3 b (CK20⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01465 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20⁻ ∷ []) ⟫ʷ
wn01465 b = lw3 b (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ []) tt tt Eq.refl
wn01466 : Base 3 → ⟪ (CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01466 b = lw3 b (CS02⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01467 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn01467 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn01468 : Base 3 → ⟪ (S1 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ []) ⟫ʷ
wn01468 b = lw0 b (S1 ∷ Toff123 ∷ []) (Toff123 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01469 : Base 3 → ⟪ (CCZ123 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ
wn01469 b = lw0 b (CCZ123 ∷ Toff123 ∷ []) (Toff123 ∷ CZ23 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01470 : Base 3 → ⟪ (CS23 ∷ CS23 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01470 b = lw0 b (CS23 ∷ CS23 ∷ CZ23 ∷ []) [] tt tt Eq.refl
wn01471 : Base 3 → ⟪ (CS13⁻ ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wn01471 b = lw0 b (CS13⁻ ∷ Toff123 ∷ []) (Toff123 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01472 : Base 3 → ⟪ (CS23⁻ ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS23⁻ ∷ []) ⟫ʷ
wn01472 b = lw0 b (CS23⁻ ∷ Toff123 ∷ []) (Toff123 ∷ CS23⁻ ∷ []) tt tt Eq.refl
wn01473 : Base 3 → ⟪ (CS23⁻ ∷ CS23⁻ ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01473 b = lw0 b (CS23⁻ ∷ CS23⁻ ∷ CZ23 ∷ []) [] tt tt Eq.refl
wn01474 : Base 3 → ⟪ (CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01474 b = lw3 b (CS12 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn01475 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ []) ⟫ʷ
wn01475 b = lw3 b (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ []) tt tt Eq.refl
wn01476 : Base 3 → ⟪ (CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01476 b = lw3 b (CK21 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) tt tt Eq.refl
wn01477 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ []) ⟫ʷ
wn01477 b = lw3 b (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ []) tt tt Eq.refl
wn01478 : Base 3 → ⟪ (CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01478 b = lw3 b (CK21⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01479 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ []) ⟫ʷ
wn01479 b = lw3 b (X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ []) tt tt Eq.refl
wn01480 : Base 3 → ⟪ (CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01480 b = lw3 b (CS12⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01481 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ []) ⟫ʷ
wn01481 b = lw3 b (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn01482 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01482 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01483 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01483 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) (S1 ∷ K1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01484 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01484 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01485 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01485 b = lw3 b (X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01486 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01486 b = lw3 b (X2 ∷ CK20⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) (S1 ∷ K1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01487 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01487 b = lw3 b (X2 ∷ CK20⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01488 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01488 b = lw3 b (X2 ∷ CK20 ∷ X2 ∷ S1 ∷ K1 ∷ []) (S1 ∷ K1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn01489 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01489 b = lw3 b (X2 ∷ CK20 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn01490 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01490 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl
wn01491 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01491 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ S1 ∷ K1 ∷ []) (S1 ∷ K1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl
wn01492 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01492 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl
wn01493 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01493 b = lw0 b (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn01494 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01494 b = lw3 b (X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn01495 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01495 b = lw0 b (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) tt tt Eq.refl
wn01496 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01496 b = lw3 b (X2 ∷ CK21 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ []) tt tt Eq.refl
wn01497 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01497 b = lw0 b (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01498 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01498 b = lw3 b (X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01499 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01499 b = lw0 b (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01500 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01500 b = lw3 b (X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01501 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01501 b = lw3 b (X2 ∷ CS12⁻ ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01502 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01502 b = lw3 b (X2 ∷ CS12⁻ ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01503 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01503 b = lw3 b (X2 ∷ CK21⁻ ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01504 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01504 b = lw3 b (X2 ∷ CK21⁻ ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01505 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01505 b = lw3 b (X2 ∷ CK21 ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) tt tt Eq.refl
wn01506 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01506 b = lw3 b (X2 ∷ CK21 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) tt tt Eq.refl
wn01507 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01507 b = lw3 b (X2 ∷ CS12 ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn01508 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01508 b = lw3 b (X2 ∷ CS12 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn01509 : Base 3 → ⟪ (K1⁻ ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01509 b = lw3 b (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl
wn01510 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K1⁻ ∷ K1 ∷ []) ⟫ʷ
wn01510 b = lw3 b [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl
wn01511 : Base 3 → ⟪ (CS12 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn01511 b = lw3 b (CS12 ∷ Toff102 ∷ []) (Toff102 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl

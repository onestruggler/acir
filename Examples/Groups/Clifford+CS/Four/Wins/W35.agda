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

module Examples.Groups.Clifford+CS.Four.Wins.W35 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)

wn01689 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01689 b = lw3 b (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn01690 : Base 3 → ⟪ (X1 ∷ Toff213 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK12 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) ⟫ʷ
wn01690 b = lw0 b (X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ CK12 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn01691 : Base 3 → ⟪ (X1 ∷ CK12 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff213 ∷ X1 ∷ []) ⟫ʷ
wn01691 b = lw0 b (X1 ∷ CK12 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ []) tt tt Eq.refl
wn01692 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CK20 ∷ []) ⟫ʷ
wn01692 b = lw3 b [] (CK20⁻ ∷ CK20 ∷ []) tt tt Eq.refl
wn01693 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (S3⁻ ∷ S3 ∷ []) ⟫ʷ
wn01693 b = lw0 b [] (S3⁻ ∷ S3 ∷ []) tt tt Eq.refl
wn01694 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01 ∷ []) ⟫ʷ
wn01694 b = lw3 b [] (CS01⁻ ∷ CS01 ∷ []) tt tt Eq.refl
wn01695 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CK10 ∷ []) ⟫ʷ
wn01695 b = lw3 b [] (CK10⁻ ∷ CK10 ∷ []) tt tt Eq.refl
wn01696 : Base 3 → ⟪ (CK20 ∷ CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01696 b = lw3 b (CK20 ∷ CK20⁻ ∷ []) [] tt tt Eq.refl
wn01697 : Base 3 → ⟪ (CX13 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01697 b = lw0 b (CX13 ∷ CX13 ∷ []) [] tt tt Eq.refl
wn01698 : Base 3 → ⟪ (CS01 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01698 b = lw3 b (CS01 ∷ CS01⁻ ∷ []) [] tt tt Eq.refl
wn01699 : Base 3 → ⟪ (CK10 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01699 b = lw3 b (CK10 ∷ CK10⁻ ∷ []) [] tt tt Eq.refl
wn01700 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn01700 b = lw3 b (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn01701 : Base 3 → ⟪ (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) ⟫ʷ
wn01701 b = lw3 b (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ []) (Sw01 ∷ X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) tt tt Eq.refl
wn01702 : Base 3 → ⟪ (Sw01 ∷ X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ []) ⟫ʷ
wn01702 b = lw3 b (Sw01 ∷ X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ []) tt tt Eq.refl
wn01703 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn01703 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn01704 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn01704 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn01705 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX12 ∷ CX12 ∷ []) ⟫ʷ
wn01705 b = lw3 b [] (CX12 ∷ CX12 ∷ []) tt tt Eq.refl
wn01706 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2 ∷ []) ⟫ʷ
wn01706 b = lw3 b [] (S2⁻ ∷ S2 ∷ []) tt tt Eq.refl
wn01707 : Base 3 → ⟪ (CX12 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01707 b = lw3 b (CX12 ∷ CX12 ∷ []) [] tt tt Eq.refl
wn01708 : Base 3 → ⟪ (S2 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01708 b = lw3 b (S2 ∷ S2⁻ ∷ []) [] tt tt Eq.refl
wn01709 : Base 3 → ⟪ (CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01709 b = lw3 b (CK20⁻ ∷ []) (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn01710 : Base 3 → ⟪ (K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ []) ⟫ʷ
wn01710 b = lw3 b (K0⁻ ∷ []) (K0⁻ ∷ []) tt tt Eq.refl
wn01711 : Base 3 → ⟪ (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
wn01711 b = lw3 b (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (CK20⁻ ∷ []) tt tt Eq.refl
wn01712 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01712 b = lw3 b (X2 ∷ CK20⁻ ∷ X2 ∷ K0⁻ ∷ []) (K0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01713 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01713 b = lw3 b (X2 ∷ CK20⁻ ∷ X2 ∷ K0 ∷ []) (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01714 : Base 3 → ⟪ (CS01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn01714 b = lw3 b (CS01 ∷ X1 ∷ []) (X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn01715 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ []) ⟫ʷ
wn01715 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ []) tt tt Eq.refl
wn01716 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn01716 b = lw3 b (CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) tt tt Eq.refl
wn01717 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
wn01717 b = lw3 b (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) tt tt Eq.refl
wn01718 : Base 3 → ⟪ (CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CK20 ∷ []) ⟫ʷ
wn01718 b = lw3 b (CK20⁻ ∷ []) (S2 ∷ CK20 ∷ []) tt tt Eq.refl
wn01719 : Base 3 → ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn01719 b = lw3 b (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn01720 : Base 3 → ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ []) ⟫ʷ
wn01720 b = lw3 b (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ []) tt tt Eq.refl
wn01721 : Base 3 → ⟪ (X0 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS01 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) ⟫ʷ
wn01721 b = lw3 b (X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS01 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) tt tt Eq.refl
wn01722 : Base 3 → ⟪ (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS01 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ
wn01722 b = lw3 b (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS01 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ []) tt tt Eq.refl
wn01723 : Base 3 → ⟪ (X0 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) ⟫ʷ
wn01723 b = lw3 b (X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) tt tt Eq.refl
wn01724 : Base 3 → ⟪ (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ
wn01724 b = lw3 b (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ []) tt tt Eq.refl
wn01725 : Base 3 → ⟪ (S1 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
wn01725 b = lw3 b (S1 ∷ CK10 ∷ []) (CK10⁻ ∷ []) tt tt Eq.refl
wn01726 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0 ∷ []) ⟫ʷ
wn01726 b = lw3 b [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn01727 : Base 3 → ⟪ (S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
wn01727 b = lw3 b (S0 ∷ []) (S0 ∷ []) tt tt Eq.refl
wn01728 : Base 3 → ⟪ (S0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01728 b = lw3 b (S0 ∷ S0⁻ ∷ []) [] tt tt Eq.refl
wn01729 : Base 3 → ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn01729 b = lw3 b (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ S0 ∷ []) tt tt Eq.refl
wn01730 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn01730 b = lw3 b (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn01731 : Base 3 → ⟪ (K1⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K0⁻ ∷ []) ⟫ʷ
wn01731 b = lw3 b (K1⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn01732 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (S0 ∷ S0⁻ ∷ []) ⟫ʷ
wn01732 b = lw3 b [] (S0 ∷ S0⁻ ∷ []) tt tt Eq.refl
wn01733 : Base 3 → ⟪ (S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn01733 b = lw3 b (S0⁻ ∷ []) (S0 ∷ S0 ∷ S0 ∷ []) tt tt Eq.refl
wn01734 : Base 3 → ⟪ (S0 ∷ S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01734 b = lw3 b (S0 ∷ S0 ∷ S0 ∷ S0 ∷ []) [] tt tt Eq.refl
wn01735 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn01735 b = lw3 b (S0 ∷ K0 ∷ []) (S0 ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ K0 ∷ []) tt tt Eq.refl
wn01736 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
wn01736 b = lw3 b (K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) tt tt Eq.refl
wn01737 : Base 3 → ⟪ (S0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ ι ∷ ι ∷ ι ∷ []) ⟫ʷ
wn01737 b = lw3 b (S0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ ι ∷ ι ∷ ι ∷ []) tt tt Eq.refl
wn01738 : Base 3 → ⟪ (ι ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ ι ∷ []) ⟫ʷ
wn01738 b = lw3 b (ι ∷ Toff012 ∷ []) (Toff012 ∷ ι ∷ []) tt tt Eq.refl
wn01739 : Base 3 → ⟪ (ι ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ ι ∷ []) ⟫ʷ
wn01739 b = lw3 b (ι ∷ CS02 ∷ []) (CS02 ∷ ι ∷ []) tt tt Eq.refl
wn01740 : Base 3 → ⟪ (ι ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ ι ∷ []) ⟫ʷ
wn01740 b = lw3 b (ι ∷ CS02⁻ ∷ []) (CS02⁻ ∷ ι ∷ []) tt tt Eq.refl
wn01741 : Base 3 → ⟪ (S0 ∷ ι ∷ ι ∷ ι ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01741 b = lw3 b (S0 ∷ ι ∷ ι ∷ ι ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) [] tt tt Eq.refl
wn01742 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn01742 b = lw3 b (S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ []) tt tt Eq.refl
wn01743 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn01743 b = lw3 b (K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn01744 : Base 3 → ⟪ (S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ []) ⟫ʷ
wn01744 b = lw3 b (S0 ∷ S0 ∷ []) (S0 ∷ S0 ∷ []) tt tt Eq.refl
wn01745 : Base 3 → ⟪ (S0 ∷ S0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01745 b = lw3 b (S0 ∷ S0 ∷ S0⁻ ∷ S0⁻ ∷ []) [] tt tt Eq.refl
wn01746 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn01746 b = lw3 b (K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0 ∷ S0 ∷ S0 ∷ []) tt tt Eq.refl
wn01747 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn01747 b = lw3 b (S0 ∷ K0 ∷ []) (S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) tt tt Eq.refl
wn01748 : Base 3 → ⟪ (CS02⁻ ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CS02⁻ ∷ []) ⟫ʷ
wn01748 b = lw3 b (CS02⁻ ∷ CX01 ∷ []) (CX01 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn01749 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01749 b = lw3 b (X2 ∷ CS12⁻ ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01750 : Base 3 → ⟪ (X3 ∷ Toff213 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CZ12 ∷ CCZ123 ∷ K2⁻ ∷ []) ⟫ʷ
wn01750 b = lw0 b (X3 ∷ Toff213 ∷ X3 ∷ []) (K2 ∷ CZ12 ∷ CCZ123 ∷ K2⁻ ∷ []) tt tt Eq.refl
wn01751 : Base 3 → ⟪ (Toff213 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) ⟫ʷ
wn01751 b = lw0 b (Toff213 ∷ []) (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) tt tt Eq.refl
wn01752 : Base 3 → ⟪ (K2⁻ ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01752 b = lw3 b (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl
wn01753 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K2⁻ ∷ K2 ∷ []) ⟫ʷ
wn01753 b = lw3 b [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl
wn01754 : Base 3 → ⟪ (K2 ∷ CZ12 ∷ CCZ123 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff213 ∷ X3 ∷ []) ⟫ʷ
wn01754 b = lw0 b (K2 ∷ CZ12 ∷ CCZ123 ∷ K2⁻ ∷ []) (X3 ∷ Toff213 ∷ X3 ∷ []) tt tt Eq.refl
wn01755 : Base 3 → ⟪ (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
wn01755 b = lw0 b (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (Toff213 ∷ []) tt tt Eq.refl
wn01756 : Base 3 → ⟪ (Toff123 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ Toff123 ∷ X2 ∷ X2 ∷ []) ⟫ʷ
wn01756 b = lw0 b (Toff123 ∷ []) (X2 ∷ X2 ∷ Toff123 ∷ X2 ∷ X2 ∷ []) tt tt Eq.refl
wn01757 : Base 3 → ⟪ (X2 ∷ X2 ∷ X3 ∷ Toff123 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ X2 ∷ []) ⟫ʷ
wn01757 b = lw0 b (X2 ∷ X2 ∷ X3 ∷ Toff123 ∷ X2 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ X2 ∷ []) tt tt Eq.refl
wn01758 : Base 3 → ⟪ (X2 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff123 ∷ X2 ∷ X3 ∷ X2 ∷ []) ⟫ʷ
wn01758 b = lw0 b (X2 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff123 ∷ X2 ∷ X3 ∷ X2 ∷ []) tt tt Eq.refl
wn01759 : Base 3 → ⟪ (X2 ∷ X2 ∷ Toff123 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn01759 b = lw0 b (X2 ∷ X2 ∷ Toff123 ∷ X2 ∷ X2 ∷ []) (Toff123 ∷ []) tt tt Eq.refl
wn01760 : Base 3 → ⟪ (X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ []) ⟫ʷ
wn01760 b = lw3 b (X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ []) tt tt Eq.refl
wn01761 : Base 3 → ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ []) ⟫ʷ
wn01761 b = lw3 b (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ []) tt tt Eq.refl
wn01762 : Base 3 → ⟪ (X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ []) ⟫ʷ
wn01762 b = lw3 b (X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ []) tt tt Eq.refl
wn01763 : Base 3 → ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X2 ∷ []) ⟫ʷ
wn01763 b = lw3 b (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X2 ∷ []) tt tt Eq.refl
wn01764 : Base 3 → ⟪ (X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ []) ⟫ʷ
wn01764 b = lw3 b (X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ []) (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ []) tt tt Eq.refl
wn01765 : Base 3 → ⟪ (X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ X2 ∷ []) ⟫ʷ
wn01765 b = lw3 b (X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ X2 ∷ []) tt tt Eq.refl
wn01766 : Base 3 → ⟪ (X2 ∷ Toff312 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) ⟫ʷ
wn01766 b = lw0 b (X2 ∷ Toff312 ∷ X2 ∷ []) (K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) tt tt Eq.refl
wn01767 : Base 3 → ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) ⟫ʷ
wn01767 b = lw0 b (Toff312 ∷ []) (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) tt tt Eq.refl
wn01768 : Base 3 → ⟪ (K3⁻ ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01768 b = lw0 b (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl
wn01769 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K3⁻ ∷ K3 ∷ []) ⟫ʷ
wn01769 b = lw0 b [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl
wn01770 : Base 3 → ⟪ (K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff312 ∷ X2 ∷ []) ⟫ʷ
wn01770 b = lw0 b (K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) (X2 ∷ Toff312 ∷ X2 ∷ []) tt tt Eq.refl
wn01771 : Base 3 → ⟪ (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wn01771 b = lw0 b (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl

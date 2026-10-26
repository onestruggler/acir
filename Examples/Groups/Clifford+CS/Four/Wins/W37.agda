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

module Examples.Groups.Clifford+CS.Four.Wins.W37 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)

wn01798 : Base 3 → ⟪ (X0 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) ⟫ʷ
wn01798 b = lw3 b (X0 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X2 ∷ []) (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) tt tt Eq.refl
wn01799 : Base 3 → ⟪ (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X2 ∷ []) ⟫ʷ
wn01799 b = lw3 b (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) (X0 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X2 ∷ []) tt tt Eq.refl
wn01800 : Base 3 → ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X1 ∷ Toff312 ∷ X1 ∷ X1 ∷ []) ⟫ʷ
wn01800 b = lw0 b (Toff312 ∷ []) (X1 ∷ X1 ∷ Toff312 ∷ X1 ∷ X1 ∷ []) tt tt Eq.refl
wn01801 : Base 3 → ⟪ (X1 ∷ X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff312 ∷ X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ
wn01801 b = lw0 b (X1 ∷ X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff312 ∷ X2 ∷ X3 ∷ X1 ∷ []) tt tt Eq.refl
wn01802 : Base 3 → ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ
wn01802 b = lw0 b (X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) tt tt Eq.refl
wn01803 : Base 3 → ⟪ (X1 ∷ X1 ∷ Toff312 ∷ X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wn01803 b = lw0 b (X1 ∷ X1 ∷ Toff312 ∷ X1 ∷ X1 ∷ []) (Toff312 ∷ []) tt tt Eq.refl
wn01804 : Base 3 → ⟪ (X0 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) ⟫ʷ
wn01804 b = lw3 b (X0 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X2 ∷ []) (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) tt tt Eq.refl
wn01805 : Base 3 → ⟪ (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X2 ∷ []) ⟫ʷ
wn01805 b = lw3 b (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) (X0 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X2 ∷ []) tt tt Eq.refl
wn01806 : Base 3 → ⟪ (CZ12 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CZ02 ∷ CZ12 ∷ []) ⟫ʷ
wn01806 b = lw3 b (CZ12 ∷ Toff102 ∷ []) (Toff102 ∷ CZ02 ∷ CZ12 ∷ []) tt tt Eq.refl
wn01807 : Base 3 → ⟪ (Z1 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ Z1 ∷ CZ02 ∷ []) ⟫ʷ
wn01807 b = lw3 b (Z1 ∷ Toff102 ∷ []) (Toff102 ∷ Z1 ∷ CZ02 ∷ []) tt tt Eq.refl
wn01808 : Base 3 → ⟪ (CZ02 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01808 b = lw3 b (CZ02 ∷ CZ02 ∷ []) [] tt tt Eq.refl
wn01809 : Base 3 → ⟪ (K2⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ K3⁻ ∷ []) ⟫ʷ
wn01809 b = lw0 b (K2⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K3⁻ ∷ []) tt tt Eq.refl
wn01810 : Base 3 → ⟪ (K3⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ K2⁻ ∷ []) ⟫ʷ
wn01810 b = lw0 b (K3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K2⁻ ∷ []) tt tt Eq.refl
wn01811 : Base 3 → ⟪ (K2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ K3 ∷ []) ⟫ʷ
wn01811 b = lw0 b (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) tt tt Eq.refl
wn01812 : Base 3 → ⟪ (CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01812 b = lw3 b (CS02⁻ ∷ []) (S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl
wn01813 : Base 3 → ⟪ (S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ []) ⟫ʷ
wn01813 b = lw3 b (S0⁻ ∷ []) (S0⁻ ∷ []) tt tt Eq.refl
wn01814 : Base 3 → ⟪ (S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wn01814 b = lw3 b (S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (CS02⁻ ∷ []) tt tt Eq.refl
wn01815 : Base 3 → ⟪ (CS02 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01815 b = lw3 b (CS02 ∷ []) (S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01816 : Base 3 → ⟪ (S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
wn01816 b = lw3 b (S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (CS02 ∷ []) tt tt Eq.refl
wn01817 : Base 3 → ⟪ (CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn01817 b = lw3 b (CS01⁻ ∷ []) (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn01818 : Base 3 → ⟪ (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
wn01818 b = lw3 b (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl
wn01819 : Base 3 → ⟪ (CS01 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn01819 b = lw3 b (CS01 ∷ []) (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn01820 : Base 3 → ⟪ (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
wn01820 b = lw3 b (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (CS01 ∷ []) tt tt Eq.refl
wn01821 : Base 3 → ⟪ (CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn01821 b = lw3 b (CS01⁻ ∷ X1 ∷ []) (X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn01822 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ []) ⟫ʷ
wn01822 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ []) tt tt Eq.refl
wn01823 : Base 3 → ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ X1 ∷ Toff312 ∷ X1 ∷ []) ⟫ʷ
wn01823 b = lw0 b (Toff312 ∷ []) (CX23 ∷ X1 ∷ Toff312 ∷ X1 ∷ []) tt tt Eq.refl
wn01824 : Base 3 → ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff312 ∷ X1 ∷ CX23 ∷ []) ⟫ʷ
wn01824 b = lw0 b (Toff312 ∷ []) (X1 ∷ Toff312 ∷ X1 ∷ CX23 ∷ []) tt tt Eq.refl
wn01825 : Base 3 → ⟪ (X1 ∷ Toff312 ∷ X1 ∷ X1 ∷ Toff312 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01825 b = lw0 b (X1 ∷ Toff312 ∷ X1 ∷ X1 ∷ Toff312 ∷ X1 ∷ []) [] tt tt Eq.refl
wn01826 : Base 3 → ⟪ (Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ X1 ∷ Toff213 ∷ X1 ∷ []) ⟫ʷ
wn01826 b = lw0 b (Toff213 ∷ []) (CX32 ∷ X1 ∷ Toff213 ∷ X1 ∷ []) tt tt Eq.refl
wn01827 : Base 3 → ⟪ (Toff213 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff213 ∷ X1 ∷ CX32 ∷ []) ⟫ʷ
wn01827 b = lw0 b (Toff213 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ CX32 ∷ []) tt tt Eq.refl
wn01828 : Base 3 → ⟪ (X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01828 b = lw0 b (X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ []) [] tt tt Eq.refl
wn01829 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn01829 b = lw3 b (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CK20 ∷ []) (CK20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) tt tt Eq.refl
wn01830 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CX12 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CX12 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wn01830 b = lw3 b (CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CX12 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CX12 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) tt tt Eq.refl
wn01831 : Base 3 → ⟪ (CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CX12 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CX12 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
wn01831 b = lw3 b (CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CX12 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CX12 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) tt tt Eq.refl
wn01832 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn01832 b = lw3 b (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ []) (S2 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn01833 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01833 b = lw3 b (X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01834 : Base 3 → ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn01834 b = lw0 b (X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn01835 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn01835 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn01836 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ K0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn01836 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ K0 ∷ K0 ∷ S0 ∷ []) (K0 ∷ K0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn01837 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn01837 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn01838 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn01838 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn01839 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn01839 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) tt tt Eq.refl
wn01840 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn01840 b = lw3 b (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn01841 : Base 3 → ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn01841 b = lw3 b (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) (K0⁻ ∷ S0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) tt tt Eq.refl
wn01842 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn01842 b = lw3 b (K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl
wn01843 : Base 3 → ⟪ (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ ι ∷ ι ∷ []) ⟫ʷ
wn01843 b = lw3 b (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ S0 ∷ ι ∷ ι ∷ []) tt tt Eq.refl
wn01844 : Base 3 → ⟪ (S0 ∷ S0 ∷ ι ∷ ι ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01844 b = lw3 b (S0 ∷ S0 ∷ ι ∷ ι ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) [] tt tt Eq.refl

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

module Examples.Groups.Clifford+CS.Four.Wins.W48 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)

wn02437 : Base 3 → ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CK31 ∷ CS12⁻ ∷ CK31⁻ ∷ []) ⟫ʷ
wn02437 b = lw0 b (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS12 ∷ CK31 ∷ CS12⁻ ∷ CK31⁻ ∷ []) tt tt Eq.refl
wn02438 : Base 3 → ⟪ (CS12 ∷ CK31 ∷ CS12⁻ ∷ CK31⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
wn02438 b = lw0 b (CS12 ∷ CK31 ∷ CS12⁻ ∷ CK31⁻ ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) tt tt Eq.refl
wn02439 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02439 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02440 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02440 b = lw3 b (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02441 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02441 b = lw3 b (K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02442 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02442 b = lw3 b (S0 ∷ K0 ∷ []) (K0 ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02443 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02443 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02444 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02444 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0 ∷ K0 ∷ K0 ∷ []) (K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02445 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02445 b = lw3 b (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02446 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ K0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02446 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ K0 ∷ K0 ∷ S0 ∷ []) (K0 ∷ K0 ∷ K0 ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02447 : Base 3 → ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02447 b = lw3 b (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn02448 : Base 3 → ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02448 b = lw3 b (S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn02449 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02449 b = lw3 b (K0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02450 : Base 3 → ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02450 b = lw3 b (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02451 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02451 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02452 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02452 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02453 : Base 3 → ⟪ (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02453 b = lw3 b (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02454 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02454 b = lw3 b (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) tt tt Eq.refl
wn02455 : Base 3 → ⟪ (S0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02455 b = lw3 b (S0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ []) tt tt Eq.refl
wn02456 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02456 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) tt tt Eq.refl
wn02457 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02457 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02458 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02458 b = lw3 b (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02459 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02459 b = lw3 b (X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02460 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02460 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02461 : Base 3 → ⟪ (S0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02461 b = lw3 b (S0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02462 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02462 b = lw3 b (K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02463 : Base 3 → ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02463 b = lw3 b (K0 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02464 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02464 b = lw3 b (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) tt tt Eq.refl
wn02465 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02465 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02466 : Base 3 → ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02466 b = lw3 b (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02467 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02467 b = lw3 b (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl
wn02468 : Base 3 → ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02468 b = lw3 b (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02469 : Base 3 → ⟪ (S0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02469 b = lw3 b (S0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) tt tt Eq.refl
wn02470 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02470 b = lw3 b (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02471 : Base 3 → ⟪ (K0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02471 b = lw3 b (K0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) tt tt Eq.refl
wn02472 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02472 b = lw3 b (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl
wn02473 : Base 3 → ⟪ (CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ []) ⟫ʷ
wn02473 b = lw3 b (CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CS02 ∷ []) (CK20⁻ ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ []) tt tt Eq.refl
wn02474 : Base 3 → ⟪ (CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ []) ⟫ʷ
wn02474 b = lw3 b (CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ []) (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ []) tt tt Eq.refl
wn02475 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02475 b = lw3 b (S0 ∷ K0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl
wn02476 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
wn02476 b = lw3 b (K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) tt tt Eq.refl
wn02477 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02477 b = lw3 b (S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (X0 ∷ S0 ∷ S0 ∷ S0 ∷ []) tt tt Eq.refl
wn02478 : Base 3 → ⟪ (S0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02478 b = lw3 b (S0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (X0 ∷ []) tt tt Eq.refl
wn02479 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02479 b = lw3 b (S0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02480 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02480 b = lw3 b (K0⁻ ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn02481 : Base 3 → ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ S0 ∷ ι ∷ ι ∷ []) ⟫ʷ
wn02481 b = lw3 b (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (X0 ∷ S0 ∷ S0 ∷ ι ∷ ι ∷ []) tt tt Eq.refl
wn02482 : Base 3 → ⟪ (S0 ∷ S0 ∷ ι ∷ ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02482 b = lw3 b (S0 ∷ S0 ∷ ι ∷ ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (X0 ∷ []) tt tt Eq.refl
wn02483 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02483 b = lw3 b [] (K0 ∷ S0 ∷ S0 ∷ K0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02484 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02484 b = lw3 b [] (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02485 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ ι ∷ []) ⟫ʷ
wn02485 b = lw3 b (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (X0 ∷ ι ∷ []) tt tt Eq.refl
wn02486 : Base 3 → ⟪ (ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02486 b = lw3 b (ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) (X0 ∷ []) tt tt Eq.refl
wn02487 : Base 3 → ⟪ (S0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02487 b = lw3 b (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl
wn02488 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02488 b = lw3 b [] (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl
wn02489 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02489 b = lw3 b [] (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02490 : Base 3 → ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ S0 ∷ ι ∷ []) ⟫ʷ
wn02490 b = lw3 b (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (X0 ∷ S0 ∷ S0 ∷ ι ∷ []) tt tt Eq.refl
wn02491 : Base 3 → ⟪ (S0 ∷ S0 ∷ ι ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02491 b = lw3 b (S0 ∷ S0 ∷ ι ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (X0 ∷ []) tt tt Eq.refl
wn02492 : Base 3 → ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02492 b = lw3 b (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl
wn02493 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02493 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02494 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02494 b = lw3 b (K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ []) [] tt tt Eq.refl
wn02495 : Base 3 → ⟪ (S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02495 b = lw3 b (S0⁻ ∷ K0 ∷ []) (S0 ∷ K0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02496 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02496 b = lw3 b (K0⁻ ∷ S0 ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02497 : Base 3 → ⟪ (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02497 b = lw3 b (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (X0 ∷ []) tt tt Eq.refl
wn02498 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02498 b = lw3 b (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (X0 ∷ []) tt tt Eq.refl
wn02499 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01 ∷ CK10 ∷ []) ⟫ʷ
wn02499 b = lw3 b (S0 ∷ K0 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01 ∷ CK10 ∷ []) tt tt Eq.refl
wn02500 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CS01⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02500 b = lw3 b (K0⁻ ∷ S0⁻ ∷ []) (CK10⁻ ∷ CS01⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02501 : Base 3 → ⟪ (CS01 ∷ CK10 ∷ CK10⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02501 b = lw3 b (CS01 ∷ CK10 ∷ CK10⁻ ∷ CS01⁻ ∷ []) [] tt tt Eq.refl
wn02502 : Base 3 → ⟪ (Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ CCZ123 ∷ CK31⁻ ∷ []) ⟫ʷ
wn02502 b = lw0 b (Toff123 ∷ []) (CK31 ∷ CCZ123 ∷ CK31⁻ ∷ []) tt tt Eq.refl
wn02503 : Base 3 → ⟪ (CK31 ∷ CCZ123 ∷ CK31⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn02503 b = lw0 b (CK31 ∷ CCZ123 ∷ CK31⁻ ∷ []) (Toff123 ∷ []) tt tt Eq.refl
wn02504 : Base 3 → ⟪ (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ []) ⟫ʷ
wn02504 b = lw3 b (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ []) tt tt Eq.refl
wn02505 : Base 3 → ⟪ (K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn02505 b = lw3 b (K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ []) (CK21 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn02506 : Base 3 → ⟪ (CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ CK21 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02506 b = lw3 b (CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ CK21 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21⁻ ∷ []) [] tt tt Eq.refl
wn02507 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CK10 ∷ CS02⁻ ∷ CK10⁻ ∷ []) ⟫ʷ
wn02507 b = lw3 b (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CK10 ∷ CS02⁻ ∷ CK10⁻ ∷ []) tt tt Eq.refl
wn02508 : Base 3 → ⟪ (CS02 ∷ CK10 ∷ CS02⁻ ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
wn02508 b = lw3 b (CS02 ∷ CK10 ∷ CS02⁻ ∷ CK10⁻ ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) tt tt Eq.refl
wn02509 : Base 3 → ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
wn02509 b = lw0 b (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13 ∷ CS13 ∷ []) tt tt Eq.refl
wn02510 : Base 3 → ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02510 b = lw0 b (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) tt tt Eq.refl
wn02511 : Base 3 → ⟪ (CS13⁻ ∷ CK31⁻ ∷ CS13 ∷ CS13 ∷ CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02511 b = lw0 b (CS13⁻ ∷ CK31⁻ ∷ CS13 ∷ CS13 ∷ CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ []) [] tt tt Eq.refl
wn02512 : Base 3 → ⟪ (S0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02512 b = lw3 b (S0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02513 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
wn02513 b = lw3 b (S0 ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02514 : Base 3 → ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02514 b = lw3 b (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02515 : Base 3 → ⟪ (K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ []) ⟫ʷ
wn02515 b = lw3 b (K0 ∷ K0 ∷ K0 ∷ []) (K0 ∷ K0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02516 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02516 b = lw3 b (K0 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn02517 : Base 3 → ⟪ (K0 ∷ K0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02517 b = lw3 b (K0 ∷ K0 ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) tt tt Eq.refl
wn02518 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02518 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02519 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02519 b = lw3 b (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02520 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02520 b = lw3 b (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) tt tt Eq.refl
wn02521 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02521 b = lw3 b (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02522 : Base 3 → ⟪ (S0⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02522 b = lw3 b (S0⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) tt tt Eq.refl
wn02523 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02523 b = lw3 b (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02524 : Base 3 → ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02524 b = lw3 b (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) tt tt Eq.refl
wn02525 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02525 b = lw3 b (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl
wn02526 : Base 3 → ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02526 b = lw3 b (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn02527 : Base 3 → ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
wn02527 b = lw3 b (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02528 : Base 3 → ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ ι ∷ ι ∷ []) ⟫ʷ
wn02528 b = lw3 b (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (X0 ∷ ι ∷ ι ∷ []) tt tt Eq.refl
wn02529 : Base 3 → ⟪ (ι ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02529 b = lw3 b (ι ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (X0 ∷ []) tt tt Eq.refl
wn02530 : Base 3 → ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02530 b = lw3 b (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0 ∷ K0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn02531 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
wn02531 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02532 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ ι ∷ []) ⟫ʷ
wn02532 b = lw3 b (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (X0 ∷ S0 ∷ ι ∷ []) tt tt Eq.refl
wn02533 : Base 3 → ⟪ (S0 ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02533 b = lw3 b (S0 ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) (X0 ∷ []) tt tt Eq.refl
wn02534 : Base 3 → ⟪ (X0 ∷ X1 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02534 b = lw3 b (X0 ∷ X1 ∷ X0 ∷ X1 ∷ []) [] tt tt Eq.refl
wn02535 : Base 3 → ⟪ (X1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ X2 ∷ []) ⟫ʷ
wn02535 b = lw3 b (X1 ∷ Sw12 ∷ []) (Sw12 ∷ X2 ∷ []) tt tt Eq.refl
wn02536 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02536 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02537 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02537 b = lw3 b (S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02538 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02538 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02539 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02539 b = lw3 b (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn02540 : Base 3 → ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02540 b = lw3 b (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) tt tt Eq.refl
wn02541 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02541 b = lw3 b (S0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02542 : Base 3 → ⟪ (S0 ∷ K0 ∷ CCZ012 ∷ CS12⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) ⟫ʷ
wn02542 b = lw3 b (S0 ∷ K0 ∷ CCZ012 ∷ CS12⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02543 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ
wn02543 b = lw3 b (S0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ []) tt tt Eq.refl
wn02544 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02544 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02545 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02545 b = lw3 b (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02546 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02546 b = lw3 b (S0 ∷ K0 ∷ S0 ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0 ∷ S0 ∷ []) tt tt Eq.refl
wn02547 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02547 b = lw3 b (S0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ []) tt tt Eq.refl
wn02548 : Base 3 → ⟪ (S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CX10 ∷ []) ⟫ʷ
wn02548 b = lw3 b (S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (CZ01 ∷ CX10 ∷ []) tt tt Eq.refl
wn02549 : Base 3 → ⟪ (S1⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S0⁻ ∷ []) ⟫ʷ
wn02549 b = lw3 b (S1⁻ ∷ Sw01 ∷ []) (Sw01 ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02550 : Base 3 → ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
wn02550 b = lw3 b (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ []) tt tt Eq.refl
wn02551 : Base 3 → ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn02551 b = lw3 b (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn02552 : Base 3 → ⟪ (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02552 b = lw3 b (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ []) [] tt tt Eq.refl
wn02553 : Base 3 → ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
wn02553 b = lw3 b (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ []) tt tt Eq.refl
wn02554 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01⁻ ∷ CK10 ∷ CS01 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02554 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (CS01⁻ ∷ CS01⁻ ∷ CK10 ∷ CS01 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02555 : Base 3 → ⟪ (CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ CS01⁻ ∷ CS01⁻ ∷ CK10 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02555 b = lw3 b (CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ CS01⁻ ∷ CS01⁻ ∷ CK10 ∷ CS01 ∷ []) [] tt tt Eq.refl
wn02556 : Base 3 → ⟪ (Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ CCZ123 ∷ CK21⁻ ∷ []) ⟫ʷ
wn02556 b = lw0 b (Toff123 ∷ []) (CK21 ∷ CCZ123 ∷ CK21⁻ ∷ []) tt tt Eq.refl
wn02557 : Base 3 → ⟪ (CK21 ∷ CCZ123 ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn02557 b = lw0 b (CK21 ∷ CCZ123 ∷ CK21⁻ ∷ []) (Toff123 ∷ []) tt tt Eq.refl
wn02558 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02558 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) [] tt tt Eq.refl
wn02559 : Base 3 → ⟪ (CS23⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS23⁻ ∷ []) ⟫ʷ
wn02559 b = lw0 b (CS23⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS23⁻ ∷ []) tt tt Eq.refl
wn02560 : Base 3 → ⟪ (Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
wn02560 b = lw0 b (Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) tt tt Eq.refl
wn02561 : Base 3 → ⟪ (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CZ01 ∷ []) ⟫ʷ
wn02561 b = lw3 b (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ []) (CX10 ∷ CZ01 ∷ []) tt tt Eq.refl
wn02562 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CZ01 ∷ CZ01 ∷ []) ⟫ʷ
wn02562 b = lw3 b [] (CZ01 ∷ CZ01 ∷ []) tt tt Eq.refl
wn02563 : Base 3 → ⟪ (CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ []) ⟫ʷ
wn02563 b = lw3 b (CZ01 ∷ []) (CS01 ∷ CS01 ∷ []) tt tt Eq.refl
wn02564 : Base 3 → ⟪ (CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wn02564 b = lw3 b (CZ01 ∷ []) (CS01⁻ ∷ CS01⁻ ∷ []) tt tt Eq.refl
wn02565 : Base 3 → ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CCZ012 ∷ CS12⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CCZ012 ∷ CS12⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX10 ∷ CZ01 ∷ X0 ∷ []) ⟫ʷ
wn02565 b = lw3 b (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CCZ012 ∷ CS12⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CCZ012 ∷ CS12⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) (X0 ∷ CX10 ∷ CZ01 ∷ X0 ∷ []) tt tt Eq.refl
wn02566 : Base 3 → ⟪ (X2 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ X2 ∷ CS01 ∷ CCZ012 ∷ CS01 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
wn02566 b = lw3 b (X2 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ X2 ∷ CS01 ∷ CCZ012 ∷ CS01 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X1 ∷ []) (S0 ∷ []) tt tt Eq.refl
wn02567 : Base 3 → ⟪ (X0 ∷ X2 ∷ CS12 ∷ CCZ012 ∷ X2 ∷ CS01 ∷ CCZ012 ∷ CS01 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ []) ⟫ʷ
wn02567 b = lw3 b (X0 ∷ X2 ∷ CS12 ∷ CCZ012 ∷ X2 ∷ CS01 ∷ CCZ012 ∷ CS01 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ []) (S1 ∷ []) tt tt Eq.refl
wn02568 : Base 3 → ⟪ (CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ []) ⟫ʷ
wn02568 b = lw3 b (CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ X0 ∷ X1 ∷ []) (S2 ∷ []) tt tt Eq.refl
wn02569 : Base 3 → ⟪ (X0 ∷ X2 ∷ CS12 ∷ CCZ012 ∷ X2 ∷ CS01 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CCZ012 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
wn02569 b = lw3 b (X0 ∷ X2 ∷ CS12 ∷ CCZ012 ∷ X2 ∷ CS01 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CCZ012 ∷ X0 ∷ X1 ∷ []) (CS01 ∷ []) tt tt Eq.refl
wn02570 : Base 3 → ⟪ (CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CCZ012 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
wn02570 b = lw3 b (CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CCZ012 ∷ X0 ∷ X1 ∷ []) (CS12 ∷ []) tt tt Eq.refl
wn02571 : Base 3 → ⟪ (CS23 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
wn02571 b = lw0 b (CS23 ∷ CCZ123 ∷ CCZ123 ∷ []) (CS23 ∷ []) tt tt Eq.refl

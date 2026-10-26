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

module Examples.Groups.Clifford+CS.Four.Wins.W47 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)

wn02345 : Base 3 → ⟪ (X2 ∷ CK23 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
wn02345 b = lw0 b (X2 ∷ CK23 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK23 ∷ X2 ∷ []) tt tt Eq.refl
wn02346 : Base 3 → ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02346 b = lw1 b (X3 ∷ CK32⁻ ∷ X3 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) tt tt Eq.refl
wn02347 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02347 b = lw0 b (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) tt tt Eq.refl
wn02348 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02348 b = lw0 b (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) tt tt Eq.refl
wn02349 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn02349 b = lw1 b (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn02350 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn02350 b = lw1 b (X3 ∷ CK32 ∷ X3 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn02351 : Base 3 → ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn02351 b = lw0 b (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn02352 : Base 3 → ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn02352 b = lw0 b (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn02353 : Base 3 → ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn02353 b = lw1 b (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CK32 ∷ X3 ∷ []) tt tt Eq.refl
wn02354 : Base 3 → ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02354 b = lw0 b (X3 ∷ CK31⁻ ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) tt tt Eq.refl
wn02355 : Base 3 → ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn02355 b = lw0 b (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn02356 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02356 b = lw0 b (X3 ∷ CK31 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) tt tt Eq.refl
wn02357 : Base 3 → ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02357 b = lw0 b (X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CK31 ∷ X3 ∷ []) tt tt Eq.refl
wn02358 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02358 b = lw3 b (K0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0 ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02359 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02359 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02360 : Base 3 → ⟪ (X1 ∷ CK10 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02360 b = lw3 b (X1 ∷ CK10 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02361 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02361 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X1 ∷ CK10 ∷ X1 ∷ []) tt tt Eq.refl
wn02362 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02362 b = lw3 b (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02363 : Base 3 → ⟪ (K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02363 b = lw3 b (K0 ∷ K0 ∷ []) (K0 ∷ K0 ∷ K0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02364 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02364 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02365 : Base 3 → ⟪ (X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02365 b = lw3 b (X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02366 : Base 3 → ⟪ (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02366 b = lw3 b (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02367 : Base 3 → ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02367 b = lw3 b (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl
wn02368 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
wn02368 b = lw3 b (K0 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ []) tt tt Eq.refl
wn02369 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02369 b = lw3 b (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) tt tt Eq.refl
wn02370 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02370 b = lw3 b (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn02371 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02371 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn02372 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02372 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02373 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02373 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02374 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02374 b = lw3 b (K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) tt tt Eq.refl
wn02375 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02375 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) tt tt Eq.refl
wn02376 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02376 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02377 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02377 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02378 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02378 b = lw3 b (K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (K0⁻ ∷ S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02379 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02379 b = lw3 b (K0 ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02380 : Base 3 → ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02380 b = lw3 b (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02381 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02381 b = lw3 b (K0 ∷ S0⁻ ∷ K0 ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn02382 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02382 b = lw3 b (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02383 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02383 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02384 : Base 3 → ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02384 b = lw3 b (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02385 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02385 b = lw3 b (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn02386 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02386 b = lw3 b (K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02387 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02387 b = lw3 b (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn02388 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02388 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02389 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02389 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02390 : Base 3 → ⟪ (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02390 b = lw3 b (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02391 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02391 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) tt tt Eq.refl
wn02392 : Base 3 → ⟪ (S0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02392 b = lw3 b (S0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl
wn02393 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02393 b = lw3 b (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn02394 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02394 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02395 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02395 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02396 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02396 b = lw3 b (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02397 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02397 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02398 : Base 3 → ⟪ (S0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02398 b = lw3 b (S0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) tt tt Eq.refl
wn02399 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02399 b = lw3 b (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn02400 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02400 b = lw3 b (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ []) (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02401 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02401 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ []) (S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02402 : Base 3 → ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02402 b = lw0 b (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) [] tt tt Eq.refl
wn02403 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02403 b = lw3 b (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) [] tt tt Eq.refl
wn02404 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02404 b = lw3 b (K0⁻ ∷ S0 ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl
wn02405 : Base 3 → ⟪ (Sw12 ∷ CCZ123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn02405 b = lw0 b (Sw12 ∷ CCZ123 ∷ Sw12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl
wn02406 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ S0⁻ ∷ []) ⟫ʷ
wn02406 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ []) (CS02 ∷ S0⁻ ∷ []) tt tt Eq.refl
wn02407 : Base 3 → ⟪ (Toff012 ∷ S0 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn02407 b = lw3 b (Toff012 ∷ S0 ∷ Toff012 ∷ []) (S0 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn02408 : Base 3 → ⟪ (S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02408 b = lw3 b (S0 ∷ S0 ∷ K0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl
wn02409 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02409 b = lw3 b (K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn02410 : Base 3 → ⟪ (S0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02410 b = lw3 b (S0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ []) tt tt Eq.refl
wn02411 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02411 b = lw3 b (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0 ∷ S0 ∷ []) tt tt Eq.refl
wn02412 : Base 3 → ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
wn02412 b = lw0 b (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ []) tt tt Eq.refl
wn02413 : Base 3 → ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS23⁻ ∷ CK32 ∷ CS23 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02413 b = lw0 b (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (CS23⁻ ∷ CS23⁻ ∷ CK32 ∷ CS23 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) tt tt Eq.refl
wn02414 : Base 3 → ⟪ (CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ CS23⁻ ∷ CS23⁻ ∷ CK32 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02414 b = lw0 b (CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ CS23⁻ ∷ CS23⁻ ∷ CK32 ∷ CS23 ∷ []) [] tt tt Eq.refl
wn02415 : Base 3 → ⟪ (CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02415 b = lw3 b (CK10⁻ ∷ X1 ∷ []) (X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02416 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ []) ⟫ʷ
wn02416 b = lw3 b (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ []) tt tt Eq.refl
wn02417 : Base 3 → ⟪ (X1 ∷ CK10 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02417 b = lw3 b (X1 ∷ CK10 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02418 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02418 b = lw3 b (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CK10 ∷ X1 ∷ []) tt tt Eq.refl
wn02419 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02419 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02420 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02420 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn02421 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn02421 b = lw3 b (X2 ∷ CK21 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn02422 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn02422 b = lw3 b (X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK21 ∷ X2 ∷ []) tt tt Eq.refl
wn02423 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CK21 ∷ CS13⁻ ∷ CK21⁻ ∷ []) ⟫ʷ
wn02423 b = lw0 b (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (CS13 ∷ CK21 ∷ CS13⁻ ∷ CK21⁻ ∷ []) tt tt Eq.refl
wn02424 : Base 3 → ⟪ (CS13 ∷ CK21 ∷ CS13⁻ ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
wn02424 b = lw0 b (CS13 ∷ CK21 ∷ CS13⁻ ∷ CK21⁻ ∷ []) (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) tt tt Eq.refl
wn02425 : Base 3 → ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ CCZ123 ∷ CK23⁻ ∷ []) ⟫ʷ
wn02425 b = lw0 b (Toff312 ∷ []) (CK23 ∷ CCZ123 ∷ CK23⁻ ∷ []) tt tt Eq.refl
wn02426 : Base 3 → ⟪ (CK23 ∷ CCZ123 ∷ CK23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wn02426 b = lw0 b (CK23 ∷ CCZ123 ∷ CK23⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl
wn02427 : Base 3 → ⟪ (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CK20⁻ ∷ []) ⟫ʷ
wn02427 b = lw3 b (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CK20⁻ ∷ []) tt tt Eq.refl
wn02428 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ CS02⁻ ∷ CS02⁻ ∷ CK20⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02428 b = lw3 b (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (CK20 ∷ CS02⁻ ∷ CS02⁻ ∷ CK20⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn02429 : Base 3 → ⟪ (CK20 ∷ CS02 ∷ CS02 ∷ CK20⁻ ∷ CK20 ∷ CS02⁻ ∷ CS02⁻ ∷ CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02429 b = lw3 b (CK20 ∷ CS02 ∷ CS02 ∷ CK20⁻ ∷ CK20 ∷ CS02⁻ ∷ CS02⁻ ∷ CK20⁻ ∷ []) [] tt tt Eq.refl
wn02430 : Base 3 → ⟪ (CK10 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02430 b = lw3 b (CK10 ∷ []) (K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn02431 : Base 3 → ⟪ (K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
wn02431 b = lw3 b (K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (CK10 ∷ []) tt tt Eq.refl
wn02432 : Base 3 → ⟪ (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ CS13 ∷ CK21⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wn02432 b = lw0 b (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (CK21 ∷ CS13 ∷ CK21⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl
wn02433 : Base 3 → ⟪ (CK21 ∷ CS13 ∷ CK21⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) ⟫ʷ
wn02433 b = lw0 b (CK21 ∷ CS13 ∷ CK21⁻ ∷ CS13⁻ ∷ []) (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) tt tt Eq.refl
wn02434 : Base 3 → ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn02434 b = lw3 b (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn02435 : Base 3 → ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ []) ⟫ʷ
wn02435 b = lw3 b (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ []) tt tt Eq.refl
wn02436 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02436 b = lw3 b (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) [] tt tt Eq.refl

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

module Examples.Groups.Clifford+CS.Four.Wins.W27 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)

wn01332 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
wn01332 b = lw0 b (CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS12 ∷ []) (CS12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) tt tt Eq.refl
wn01333 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK12⁻ ∷ X1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
wn01333 b = lw0 b (CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) (X1 ∷ CK12⁻ ∷ X1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) tt tt Eq.refl
wn01334 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
wn01334 b = lw0 b (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) tt tt Eq.refl
wn01335 : Base 3 → ⟪ (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ []) ⟫ʷ
wn01335 b = lw3 b (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (ι ∷ []) tt tt Eq.refl
wn01336 : Base 3 → ⟪ (K0⁻ ∷ CZ02 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
wn01336 b = lw3 b (K0⁻ ∷ CZ02 ∷ K0 ∷ []) (CX20 ∷ []) tt tt Eq.refl
wn01337 : Base 3 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn01337 b = lw0 b (CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl
wn01338 : Base 3 → ⟪ (K0 ∷ CX20 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
wn01338 b = lw3 b (K0 ∷ CX20 ∷ K0⁻ ∷ []) (CZ02 ∷ []) tt tt Eq.refl
wn01339 : Base 3 → ⟪ (K0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01339 b = lw3 b (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl
wn01340 : Base 3 → ⟪ (CX23 ∷ CS13 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12 ∷ CCZ123 ∷ []) ⟫ʷ
wn01340 b = lw0 b (CX23 ∷ CS13 ∷ CX23 ∷ []) (CS13 ∷ CS12 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn01341 : Base 3 → ⟪ (CX23 ∷ CS13⁻ ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS12⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wn01341 b = lw0 b (CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CCZ123 ∷ CS12⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl
wn01342 : Base 3 → ⟪ (CS02 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01342 b = lw3 b (CS02 ∷ CS02⁻ ∷ []) [] tt tt Eq.refl
wn01343 : Base 3 → ⟪ (CCZ012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) ⟫ʷ
wn01343 b = lw3 b (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) tt tt Eq.refl
wn01344 : Base 3 → ⟪ (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
wn01344 b = lw3 b (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01345 : Base 3 → ⟪ (CZ12 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CZ12 ∷ []) ⟫ʷ
wn01345 b = lw3 b (CZ12 ∷ CS02 ∷ []) (CS02 ∷ CZ12 ∷ []) tt tt Eq.refl
wn01346 : Base 3 → ⟪ (CZ12 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CZ12 ∷ []) ⟫ʷ
wn01346 b = lw3 b (CZ12 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CZ12 ∷ []) tt tt Eq.refl
wn01347 : Base 3 → ⟪ (Toff102 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) ⟫ʷ
wn01347 b = lw3 b (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) tt tt Eq.refl
wn01348 : Base 3 → ⟪ (K1⁻ ∷ CZ13 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
wn01348 b = lw0 b (K1⁻ ∷ CZ13 ∷ K1 ∷ []) (CX31 ∷ []) tt tt Eq.refl
wn01349 : Base 3 → ⟪ (K1 ∷ CX31 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ []) ⟫ʷ
wn01349 b = lw0 b (K1 ∷ CX31 ∷ K1⁻ ∷ []) (CZ13 ∷ []) tt tt Eq.refl
wn01350 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ
wn01350 b = lw0 b [] (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) tt tt Eq.refl
wn01351 : Base 3 → ⟪ (CS02 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS02 ∷ []) ⟫ʷ
wn01351 b = lw3 b (CS02 ∷ Toff102 ∷ []) (Toff102 ∷ CS02 ∷ []) tt tt Eq.refl
wn01352 : Base 3 → ⟪ (CS02⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS02⁻ ∷ []) ⟫ʷ
wn01352 b = lw3 b (CS02⁻ ∷ Toff102 ∷ []) (Toff102 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn01353 : Base 3 → ⟪ (S2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ S2 ∷ []) ⟫ʷ
wn01353 b = lw3 b (S2 ∷ Toff102 ∷ []) (Toff102 ∷ S2 ∷ []) tt tt Eq.refl
wn01354 : Base 3 → ⟪ (S2⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ S2⁻ ∷ []) ⟫ʷ
wn01354 b = lw3 b (S2⁻ ∷ Toff102 ∷ []) (Toff102 ∷ S2⁻ ∷ []) tt tt Eq.refl
wn01355 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CK20 ∷ CK20⁻ ∷ []) ⟫ʷ
wn01355 b = lw3 b [] (CK20 ∷ CK20⁻ ∷ []) tt tt Eq.refl
wn01356 : Base 3 → ⟪ (CK20⁻ ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01356 b = lw3 b (CK20⁻ ∷ CK20 ∷ []) [] tt tt Eq.refl
wn01357 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CS02 ∷ CS02⁻ ∷ []) ⟫ʷ
wn01357 b = lw3 b [] (CS02 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn01358 : Base 3 → ⟪ (CS02⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01358 b = lw3 b (CS02⁻ ∷ CS02 ∷ []) [] tt tt Eq.refl
wn01359 : Base 3 → ⟪ (X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ Toff102 ∷ []) ⟫ʷ
wn01359 b = lw3 b (X2 ∷ Toff102 ∷ X2 ∷ []) (CX01 ∷ Toff102 ∷ []) tt tt Eq.refl
wn01360 : Base 3 → ⟪ (CS02 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CS02 ∷ []) ⟫ʷ
wn01360 b = lw3 b (CS02 ∷ CX01 ∷ []) (CX01 ∷ CS02 ∷ []) tt tt Eq.refl
wn01361 : Base 3 → ⟪ (CX01 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ
wn01361 b = lw3 b (CX01 ∷ Toff102 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ []) tt tt Eq.refl
wn01362 : Base 3 → ⟪ (X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ Toff012 ∷ []) ⟫ʷ
wn01362 b = lw3 b (X2 ∷ Toff012 ∷ X2 ∷ []) (CX10 ∷ Toff012 ∷ []) tt tt Eq.refl
wn01363 : Base 3 → ⟪ (CS02 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn01363 b = lw3 b (CS02 ∷ CX10 ∷ []) (CX10 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn01364 : Base 3 → ⟪ (CX10 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ
wn01364 b = lw3 b (CX10 ∷ Toff012 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ []) tt tt Eq.refl
wn01365 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01365 b = lw0 b (CS13 ∷ CS13 ∷ CZ13 ∷ []) [] tt tt Eq.refl
wn01366 : Base 3 → ⟪ (CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn01366 b = lw0 b (CK31 ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) tt tt Eq.refl
wn01367 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ []) ⟫ʷ
wn01367 b = lw0 b (X3 ∷ CK31 ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ []) tt tt Eq.refl
wn01368 : Base 3 → ⟪ (S0 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ S0 ∷ []) ⟫ʷ
wn01368 b = lw3 b (S0 ∷ Toff102 ∷ []) (Toff102 ∷ S0 ∷ []) tt tt Eq.refl
wn01369 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CK31 ∷ CK31⁻ ∷ []) ⟫ʷ
wn01369 b = lw0 b [] (CK31 ∷ CK31⁻ ∷ []) tt tt Eq.refl
wn01370 : Base 3 → ⟪ (CK31⁻ ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01370 b = lw0 b (CK31⁻ ∷ CK31 ∷ []) [] tt tt Eq.refl
wn01371 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CK32 ∷ CK32⁻ ∷ []) ⟫ʷ
wn01371 b = lw0 b [] (CK32 ∷ CK32⁻ ∷ []) tt tt Eq.refl
wn01372 : Base 3 → ⟪ (CK32⁻ ∷ CK32 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01372 b = lw0 b (CK32⁻ ∷ CK32 ∷ []) [] tt tt Eq.refl
wn01373 : Base 3 → ⟪ (X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ Toff123 ∷ []) ⟫ʷ
wn01373 b = lw0 b (X3 ∷ Toff123 ∷ X3 ∷ []) (CX21 ∷ Toff123 ∷ []) tt tt Eq.refl
wn01374 : Base 3 → ⟪ (CS23 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS23 ∷ []) ⟫ʷ
wn01374 b = lw0 b (CS23 ∷ Toff123 ∷ []) (Toff123 ∷ CS23 ∷ []) tt tt Eq.refl
wn01375 : Base 3 → ⟪ (CX21 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ
wn01375 b = lw0 b (CX21 ∷ Toff123 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ []) tt tt Eq.refl
wn01376 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CS13 ∷ CS13⁻ ∷ []) ⟫ʷ
wn01376 b = lw0 b [] (CS13 ∷ CS13⁻ ∷ []) tt tt Eq.refl
wn01377 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Toff102 ∷ Toff102 ∷ []) ⟫ʷ
wn01377 b = lw3 b [] (Toff102 ∷ Toff102 ∷ []) tt tt Eq.refl
wn01378 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS13 ∷ []) ⟫ʷ
wn01378 b = lw0 b [] (CS13⁻ ∷ CS13 ∷ []) tt tt Eq.refl
wn01379 : Base 3 → ⟪ (CS13⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01379 b = lw0 b (CS13⁻ ∷ CS13 ∷ []) [] tt tt Eq.refl
wn01380 : Base 3 → ⟪ (Toff102 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01380 b = lw3 b (Toff102 ∷ Toff102 ∷ []) [] tt tt Eq.refl
wn01381 : Base 3 → ⟪ (CS13 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01381 b = lw0 b (CS13 ∷ CS13⁻ ∷ []) [] tt tt Eq.refl
wn01382 : Base 3 → ⟪ (CS12 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CS12 ∷ []) ⟫ʷ
wn01382 b = lw3 b (CS12 ∷ CX10 ∷ []) (CX10 ∷ CS12 ∷ []) tt tt Eq.refl
wn01383 : Base 3 → ⟪ (S0⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ S0⁻ ∷ []) ⟫ʷ
wn01383 b = lw3 b (S0⁻ ∷ Toff201 ∷ []) (Toff201 ∷ S0⁻ ∷ []) tt tt Eq.refl
wn01384 : Base 3 → ⟪ (S2⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S2⁻ ∷ []) ⟫ʷ
wn01384 b = lw3 b (S2⁻ ∷ Toff012 ∷ []) (Toff012 ∷ S2⁻ ∷ []) tt tt Eq.refl
wn01385 : Base 3 → ⟪ (S2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S2 ∷ []) ⟫ʷ
wn01385 b = lw3 b (S2 ∷ Toff012 ∷ []) (Toff012 ∷ S2 ∷ []) tt tt Eq.refl
wn01386 : Base 3 → ⟪ (X0 ∷ CX10 ∷ CX20 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
wn01386 b = lw3 b (X0 ∷ CX10 ∷ CX20 ∷ Toff012 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) tt tt Eq.refl
wn01387 : Base 3 → ⟪ (CS13 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01387 b = lw0 b (CS13 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ []) [] tt tt Eq.refl
wn01388 : Base 3 → ⟪ (S0 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ S0 ∷ []) ⟫ʷ
wn01388 b = lw3 b (S0 ∷ Toff201 ∷ []) (Toff201 ∷ S0 ∷ []) tt tt Eq.refl
wn01389 : Base 3 → ⟪ (Toff213 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) ⟫ʷ
wn01389 b = lw0 b (Toff213 ∷ []) (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) tt tt Eq.refl
wn01390 : Base 3 → ⟪ (X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ
wn01390 b = lw0 b (X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) tt tt Eq.refl
wn01391 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ []) ⟫ʷ
wn01391 b = lw0 b (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ []) tt tt Eq.refl
wn01392 : Base 3 → ⟪ (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
wn01392 b = lw0 b (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) (Toff213 ∷ []) tt tt Eq.refl
wn01393 : Base 3 → ⟪ (X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ
wn01393 b = lw0 b (X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) tt tt Eq.refl
wn01394 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ X3 ∷ []) ⟫ʷ
wn01394 b = lw0 b (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ X3 ∷ []) tt tt Eq.refl
wn01395 : Base 3 → ⟪ (X2 ∷ Toff123 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CZ13 ∷ CS23 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01395 b = lw0 b (X2 ∷ Toff123 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CZ13 ∷ CS23 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn01396 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ CZ13 ∷ CS23 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff123 ∷ X2 ∷ []) ⟫ʷ
wn01396 b = lw0 b (X2 ∷ CK21 ∷ X2 ∷ CZ13 ∷ CS23 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ Toff123 ∷ X2 ∷ []) tt tt Eq.refl
wn01397 : Base 3 → ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ CS12 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ []) ⟫ʷ
wn01397 b = lw0 b (Toff312 ∷ []) (CK23 ∷ CS12 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ []) tt tt Eq.refl
wn01398 : Base 3 → ⟪ (CK23 ∷ CS12 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wn01398 b = lw0 b (CK23 ∷ CS12 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl
wn01399 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn01399 b = lw0 b (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) tt tt Eq.refl
wn01400 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ
wn01400 b = lw0 b (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) tt tt Eq.refl
wn01401 : Base 3 → ⟪ (X3 ∷ Toff213 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ X3 ∷ CZ12 ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn01401 b = lw0 b (X3 ∷ Toff213 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ CZ12 ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn01402 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ CZ12 ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff213 ∷ X3 ∷ []) ⟫ʷ
wn01402 b = lw0 b (X3 ∷ CK32 ∷ X3 ∷ CZ12 ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ Toff213 ∷ X3 ∷ []) tt tt Eq.refl
wn01403 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
wn01403 b = lw0 b (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) tt tt Eq.refl
wn01404 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ
wn01404 b = lw0 b (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) tt tt Eq.refl
wn01405 : Base 3 → ⟪ (X1 ∷ Toff312 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK13 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
wn01405 b = lw0 b (X1 ∷ Toff312 ∷ X1 ∷ []) (X1 ∷ CK13 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn01406 : Base 3 → ⟪ (X1 ∷ CK13 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff312 ∷ X1 ∷ []) ⟫ʷ
wn01406 b = lw0 b (X1 ∷ CK13 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (X1 ∷ Toff312 ∷ X1 ∷ []) tt tt Eq.refl
wn01407 : Base 3 → ⟪ (CK20 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01407 b = lw3 b (CK20 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn01408 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ []) ⟫ʷ
wn01408 b = lw3 b (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ []) tt tt Eq.refl
wn01409 : Base 3 → ⟪ (CK32 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn01409 b = lw0 b (CK32 ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK32 ∷ X3 ∷ []) tt tt Eq.refl
wn01410 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ []) ⟫ʷ
wn01410 b = lw0 b (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ []) tt tt Eq.refl
wn01411 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01411 b = lw3 b (X2 ∷ CK20 ∷ X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn01412 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn01412 b = lw0 b (X3 ∷ CK31 ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CK31 ∷ X3 ∷ []) tt tt Eq.refl
wn01413 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01413 b = lw3 b (X2 ∷ CK20 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn01414 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn01414 b = lw1 b (X3 ∷ CK32 ∷ X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ CK32 ∷ X3 ∷ []) tt tt Eq.refl
wn01415 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn01415 b = lw0 b (X3 ∷ CK32 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ []) tt tt Eq.refl
wn01416 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ CS02 ∷ CK10⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wn01416 b = lw3 b (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (CK10 ∷ CS02 ∷ CK10⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn01417 : Base 3 → ⟪ (CK10 ∷ CS02 ∷ CK10⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn01417 b = lw3 b (CK10 ∷ CS02 ∷ CK10⁻ ∷ CS02⁻ ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn01418 : Base 3 → ⟪ (S1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S1 ∷ []) ⟫ʷ
wn01418 b = lw3 b (S1 ∷ Toff012 ∷ []) (Toff012 ∷ S1 ∷ []) tt tt Eq.refl
wn01419 : Base 3 → ⟪ (X1 ∷ CX10 ∷ X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) ⟫ʷ
wn01419 b = lw3 b (X1 ∷ CX10 ∷ X1 ∷ X0 ∷ []) (X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) tt tt Eq.refl
wn01420 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ []) ⟫ʷ
wn01420 b = lw0 b (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ []) (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ []) tt tt Eq.refl

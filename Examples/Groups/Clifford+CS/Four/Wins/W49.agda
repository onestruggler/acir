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

module Examples.Groups.Clifford+CS.Four.Wins.W49 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)

wn02572 : Base 3 → ⟪ (S0 ∷ S0 ∷ X0 ∷ X1 ∷ X2 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X1 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X1 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02572 b = lw3 b (S0 ∷ S0 ∷ X0 ∷ X1 ∷ X2 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X1 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X1 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X0 ∷ X1 ∷ []) (X0 ∷ []) tt tt Eq.refl
wn02573 : Base 3 → ⟪ (S2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S1⁻ ∷ []) ⟫ʷ
wn02573 b = lw3 b (S2⁻ ∷ Sw12 ∷ []) (Sw12 ∷ S1⁻ ∷ []) tt tt Eq.refl
wn02574 : Base 3 → ⟪ (K2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ K1⁻ ∷ []) ⟫ʷ
wn02574 b = lw3 b (K2⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K1⁻ ∷ []) tt tt Eq.refl
wn02575 : Base 3 → ⟪ (S1 ∷ S1 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X0 ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
wn02575 b = lw3 b (S1 ∷ S1 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X0 ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X0 ∷ X1 ∷ []) (X1 ∷ []) tt tt Eq.refl
wn02576 : Base 3 → ⟪ (S2 ∷ S2 ∷ X0 ∷ X2 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
wn02576 b = lw3 b (S2 ∷ S2 ∷ X0 ∷ X2 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X1 ∷ X2 ∷ []) (X2 ∷ []) tt tt Eq.refl
wn02577 : Base 3 → ⟪ (S2 ∷ S2 ∷ X0 ∷ X1 ∷ X2 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
wn02577 b = lw3 b (S2 ∷ S2 ∷ X0 ∷ X1 ∷ X2 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ []) (X2 ∷ []) tt tt Eq.refl
wn02578 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (S1 ∷ S1⁻ ∷ []) ⟫ʷ
wn02578 b = lw3 b [] (S1 ∷ S1⁻ ∷ []) tt tt Eq.refl
wn02579 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K1 ∷ K1⁻ ∷ []) ⟫ʷ
wn02579 b = lw3 b [] (K1 ∷ K1⁻ ∷ []) tt tt Eq.refl
wn02580 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1 ∷ []) ⟫ʷ
wn02580 b = lw3 b [] (S1⁻ ∷ S1 ∷ []) tt tt Eq.refl
wn02581 : Base 3 → ⟪ (S1⁻ ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02581 b = lw3 b (S1⁻ ∷ S1 ∷ []) [] tt tt Eq.refl
wn02582 : Base 3 → ⟪ (K1 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02582 b = lw3 b (K1 ∷ K1⁻ ∷ []) [] tt tt Eq.refl
wn02583 : Base 3 → ⟪ (S1 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02583 b = lw3 b (S1 ∷ S1⁻ ∷ []) [] tt tt Eq.refl
wn02584 : Base 3 → ⟪ (CX10 ∷ CZ01 ∷ CZ01 ∷ CX01 ∷ CX10 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Sw01 ∷ []) ⟫ʷ
wn02584 b = lw3 b (CX10 ∷ CZ01 ∷ CZ01 ∷ CX01 ∷ CX10 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl

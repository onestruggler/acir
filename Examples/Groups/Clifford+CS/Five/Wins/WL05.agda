------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL05 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl0788 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) ⟫ʷ
wl0788 c4 = lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl

wl0789 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) ⟫ʷ
wl0789 c4 = lw0 c4 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0790 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) ⟫ʷ
wl0790 c4 = lw0 c4 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0791 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) ⟫ʷ
wl0791 c4 = lw0 c4 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0792 : Complete 4 → ⟪ (K2⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ K2⁻ ∷ []) ⟫ʷ
wl0792 c4 = lw4 c4 (K2⁻ ∷ Toff013 ∷ []) (Toff013 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0793 : Complete 4 → ⟪ (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) ⟫ʷ
wl0793 c4 = lw0 c4 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0794 : Complete 4 → ⟪ (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) ⟫ʷ
wl0794 c4 = lw0 c4 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0795 : Complete 4 → ⟪ (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) ⟫ʷ
wl0795 c4 = lw0 c4 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0796 : Complete 4 → ⟪ (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0796 c4 = lw1 c4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0797 : Complete 4 → ⟪ (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0797 c4 = lw0 c4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0798 : Complete 4 → ⟪ (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0798 c4 = lw1 c4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0799 : Complete 4 → ⟪ (CS12 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS12 ∷ []) ⟫ʷ
wl0799 c4 = lw4 c4 (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) tt tt Eq.refl

wl0800 : Complete 4 → ⟪ (CS02 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS02 ∷ []) ⟫ʷ
wl0800 c4 = lw3 c4 (CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ []) tt tt Eq.refl

wl0801 : Complete 4 → ⟪ (CS02⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS02⁻ ∷ []) ⟫ʷ
wl0801 c4 = lw3 c4 (CS02⁻ ∷ X4 ∷ []) (X4 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl0802 : Complete 4 → ⟪ (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ
wl0802 c4 = lw0 c4 (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ []) (X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl

wl0803 : Complete 4 → ⟪ (CCZ124 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ []) ⟫ʷ
wl0803 c4 = lw0 c4 (CCZ124 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ []) (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0804 : Complete 4 → ⟪ (CCZ124 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ []) ⟫ʷ
wl0804 c4 = lw0 c4 (CCZ124 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ []) (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0805 : Complete 4 → ⟪ (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
wl0805 c4 = lw0 c4 (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS12 ∷ []) tt tt Eq.refl

wl0806 : Complete 4 → ⟪ (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0806 c4 = lw4 c4 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ []) [] tt tt Eq.refl

wl0807 : Complete 4 → ⟪ (CS13 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0807 c4 = lw4 c4 (CS13 ∷ CS13⁻ ∷ []) [] tt tt Eq.refl

wl0808 : Complete 4 → ⟪ (CS13⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0808 c4 = lw4 c4 (CS13⁻ ∷ CS13 ∷ []) [] tt tt Eq.refl

wl0809 : Complete 4 → ⟪ (CCZ012 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wl0809 c4 = lw4 c4 (CCZ012 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0810 : Complete 4 → ⟪ (CCZ012 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wl0810 c4 = lw4 c4 (CCZ012 ∷ CS12 ∷ []) (CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0811 : Complete 4 → ⟪ (Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ []) ⟫ʷ
wl0811 c4 = lw4 c4 (Toff023 ∷ []) (Toff023 ∷ []) tt tt Eq.refl

wl0812 : Complete 4 → ⟪ (Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ []) ⟫ʷ
wl0812 c4 = lw0 c4 (Toff423 ∷ []) (Toff423 ∷ []) tt tt Eq.refl

wl0813 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wl0813 c4 = lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl

wl0814 : Complete 4 → ⟪ (CS12⁻ ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wl0814 c4 = lw0 c4 (CS12⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0815 : Complete 4 → ⟪ (CS12⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0815 c4 = lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0816 : Complete 4 → ⟪ (CS12⁻ ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0816 c4 = lw0 c4 (CS12⁻ ∷ CS14 ∷ []) (CS14 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0817 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) ⟫ʷ
wl0817 c4 = lw0 c4 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0818 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) ⟫ʷ
wl0818 c4 = lw0 c4 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0819 : Complete 4 → ⟪ (CCZ023 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wl0819 c4 = lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0820 : Complete 4 → ⟪ (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) ⟫ʷ
wl0820 c4 = lw0 c4 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0821 : Complete 4 → ⟪ (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) ⟫ʷ
wl0821 c4 = lw0 c4 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0822 : Complete 4 → ⟪ (CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX23 ∷ X4 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0822 c4 = lw0 c4 (CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ X4 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0823 : Complete 4 → ⟪ (CCZ023 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ023 ∷ []) ⟫ʷ
wl0823 c4 = lw4 c4 (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0824 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12⁻ ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0824 c4 = lw0 c4 (S4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0825 : Complete 4 → ⟪ (S4 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0825 c4 = lw0 c4 (S4 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0826 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0826 c4 = lw0 c4 (S4 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0827 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0827 c4 = lw0 c4 (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0828 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0828 c4 = lw0 c4 (CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0829 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0829 c4 = lw0 c4 (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0830 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12⁻ ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0830 c4 = lw0 c4 (CS24 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0831 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0831 c4 = lw0 c4 (CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0832 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0832 c4 = lw0 c4 (CS24 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0833 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) ⟫ʷ
wl0833 c4 = lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl

wl0834 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0834 c4 = lw0 c4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0835 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0835 c4 = lw0 c4 (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0836 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0836 c4 = lw0 c4 (CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0837 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0837 c4 = lw0 c4 (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0838 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12⁻ ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wl0838 c4 = lw0 c4 (S4⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0839 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wl0839 c4 = lw0 c4 (S4⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0840 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wl0840 c4 = lw0 c4 (S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0841 : Complete 4 → ⟪ (K1 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K1 ∷ []) ⟫ʷ
wl0841 c4 = lw0 c4 (K1 ∷ X4 ∷ []) (X4 ∷ K1 ∷ []) tt tt Eq.refl

wl0842 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) ⟫ʷ
wl0842 c4 = lw0 c4 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) tt tt Eq.refl

wl0843 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) ⟫ʷ
wl0843 c4 = lw0 c4 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) tt tt Eq.refl

wl0844 : Complete 4 → ⟪ (CCZ013 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CCZ013 ∷ []) ⟫ʷ
wl0844 c4 = lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0845 : Complete 4 → ⟪ (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) ⟫ʷ
wl0845 c4 = lw0 c4 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) tt tt Eq.refl

wl0846 : Complete 4 → ⟪ (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) ⟫ʷ
wl0846 c4 = lw0 c4 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) tt tt Eq.refl

wl0847 : Complete 4 → ⟪ (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) ⟫ʷ
wl0847 c4 = lw0 c4 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) tt tt Eq.refl

wl0848 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0848 c4 = lw1 c4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0849 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0849 c4 = lw0 c4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0850 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0850 c4 = lw2 c4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0851 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0851 c4 = lw2 c4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0852 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K0 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0852 c4 = lw1 c4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0853 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) ⟫ʷ
wl0853 c4 = lw0 c4 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0854 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) ⟫ʷ
wl0854 c4 = lw0 c4 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0855 : Complete 4 → ⟪ (CCZ013 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wl0855 c4 = lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0856 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) ⟫ʷ
wl0856 c4 = lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) tt tt Eq.refl

wl0857 : Complete 4 → ⟪ (CS24⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0857 c4 = lw0 c4 (CS24⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0858 : Complete 4 → ⟪ (CCZ013 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ013 ∷ []) ⟫ʷ
wl0858 c4 = lw4 c4 (CCZ013 ∷ CS02 ∷ []) (CS02 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0859 : Complete 4 → ⟪ (K3⁻ ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0859 c4 = lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl

wl0860 : Complete 4 → ⟪ (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) ⟫ʷ
wl0860 c4 = lw0 c4 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0861 : Complete 4 → ⟪ (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) ⟫ʷ
wl0861 c4 = lw0 c4 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0862 : Complete 4 → ⟪ (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) ⟫ʷ
wl0862 c4 = lw0 c4 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0863 : Complete 4 → ⟪ (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) ⟫ʷ
wl0863 c4 = lw0 c4 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0864 : Complete 4 → ⟪ (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) ⟫ʷ
wl0864 c4 = lw0 c4 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0865 : Complete 4 → ⟪ (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) ⟫ʷ
wl0865 c4 = lw0 c4 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0866 : Complete 4 → ⟪ (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0866 c4 = lw1 c4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0867 : Complete 4 → ⟪ (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0867 c4 = lw0 c4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0868 : Complete 4 → ⟪ (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS01⁻ ∷ X4 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0868 c4 = lw2 c4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0869 : Complete 4 → ⟪ (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0869 c4 = lw2 c4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0870 : Complete 4 → ⟪ (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0870 c4 = lw1 c4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0871 : Complete 4 → ⟪ (CCZ013 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wl0871 c4 = lw4 c4 (CCZ013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0872 : Complete 4 → ⟪ (CCZ013 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ013 ∷ []) ⟫ʷ
wl0872 c4 = lw4 c4 (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0873 : Complete 4 → ⟪ (CCZ012 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wl0873 c4 = lw4 c4 (CCZ012 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0874 : Complete 4 → ⟪ (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) ⟫ʷ
wl0874 c4 = lw0 c4 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0875 : Complete 4 → ⟪ (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) ⟫ʷ
wl0875 c4 = lw0 c4 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0876 : Complete 4 → ⟪ (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) ⟫ʷ
wl0876 c4 = lw0 c4 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0877 : Complete 4 → ⟪ (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ
wl0877 c4 = lw0 c4 (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ []) (X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl

wl0878 : Complete 4 → ⟪ (CCZ234 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ []) ⟫ʷ
wl0878 c4 = lw0 c4 (CCZ234 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ []) (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0879 : Complete 4 → ⟪ (CCZ234 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CCZ234 ∷ []) ⟫ʷ
wl0879 c4 = lw0 c4 (CCZ234 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ []) (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0880 : Complete 4 → ⟪ (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
wl0880 c4 = lw0 c4 (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS23 ∷ []) tt tt Eq.refl

wl0881 : Complete 4 → ⟪ (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0881 c4 = lw4 c4 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ []) [] tt tt Eq.refl

wl0882 : Complete 4 → ⟪ (CS12 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0882 c4 = lw4 c4 (CS12 ∷ CS12⁻ ∷ []) [] tt tt Eq.refl

wl0883 : Complete 4 → ⟪ (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) ⟫ʷ
wl0883 c4 = lw0 c4 (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) tt tt Eq.refl

wl0884 : Complete 4 → ⟪ (CS14 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) ⟫ʷ
wl0884 c4 = lw0 c4 (CS14 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) tt tt Eq.refl

wl0885 : Complete 4 → ⟪ (K1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0885 c4 = lw0 c4 (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0886 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ []) ⟫ʷ
wl0886 c4 = lw1 c4 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) tt tt Eq.refl

wl0887 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0887 c4 = lw0 c4 (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0888 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0888 c4 = lw0 c4 (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0889 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0889 c4 = lw0 c4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0890 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0890 c4 = lw0 c4 (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0891 : Complete 4 → ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0891 c4 = lw0 c4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0892 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0892 c4 = lw0 c4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0893 : Complete 4 → ⟪ (S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0893 c4 = lw0 c4 (S2 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0894 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0894 c4 = lw0 c4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0895 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0895 c4 = lw0 c4 (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0896 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0896 c4 = lw0 c4 (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0897 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0897 c4 = lw0 c4 (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0898 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0898 c4 = lw0 c4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0899 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0899 c4 = lw0 c4 (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0900 : Complete 4 → ⟪ (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0900 c4 = lw0 c4 (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) [] tt tt Eq.refl

wl0901 : Complete 4 → ⟪ (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0901 c4 = lw0 c4 (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) [] tt tt Eq.refl

wl0902 : Complete 4 → ⟪ (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0902 c4 = lw0 c4 (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) [] tt tt Eq.refl

wl0903 : Complete 4 → ⟪ (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0903 c4 = lw0 c4 (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) [] tt tt Eq.refl

wl0904 : Complete 4 → ⟪ (CK41 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wl0904 c4 = lw0 c4 (CK41 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wl0905 : Complete 4 → ⟪ (CK42 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wl0905 c4 = lw0 c4 (CK42 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wl0906 : Complete 4 → ⟪ (CK43 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wl0906 c4 = lw0 c4 (CK43 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

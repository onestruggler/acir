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

module Examples.Groups.Clifford+CS.Four.Wins.W02 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)

wn00216 : Base 3 → ⟪ (CS01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS01 ∷ []) ⟫ʷ
wn00216 b = lw3 b (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) tt tt Eq.refl
wn00217 : Base 3 → ⟪ (X1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ X0 ∷ []) ⟫ʷ
wn00217 b = lw3 b (X1 ∷ Sw01 ∷ []) (Sw01 ∷ X0 ∷ []) tt tt Eq.refl
wn00218 : Base 3 → ⟪ (CK10 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK01 ∷ []) ⟫ʷ
wn00218 b = lw3 b (CK10 ∷ Sw01 ∷ []) (Sw01 ∷ CK01 ∷ []) tt tt Eq.refl
wn00219 : Base 3 → ⟪ (Sw01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sw01 ∷ []) ⟫ʷ
wn00219 b = lw3 b (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00220 : Base 3 → ⟪ (Sw01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Sw01 ∷ []) ⟫ʷ
wn00220 b = lw3 b (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00221 : Base 3 → ⟪ (Sw01 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ Sw01 ∷ []) ⟫ʷ
wn00221 b = lw3 b (Sw01 ∷ CK01 ∷ []) (CK10 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00222 : Base 3 → ⟪ (Sw12 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Sw12 ∷ []) ⟫ʷ
wn00222 b = lw3 b (Sw12 ∷ X1 ∷ []) (X2 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00223 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn00223 b = lw3 b (X2 ∷ CK20 ∷ X2 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn00224 : Base 3 → ⟪ (K0 ∷ Toff012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wn00224 b = lw3 b (K0 ∷ Toff012 ∷ K0⁻ ∷ []) (CCZ012 ∷ []) tt tt Eq.refl
wn00225 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ
wn00225 b = lw0 b [] (X3 ∷ X3 ∷ []) tt tt Eq.refl
wn00226 : Base 3 → ⟪ (CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff012 ∷ []) ⟫ʷ
wn00226 b = lw3 b (CCZ012 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff012 ∷ []) tt tt Eq.refl
wn00227 : Base 3 → ⟪ (Toff012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00227 b = lw3 b (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl
wn00228 : Base 3 → ⟪ (Toff012 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CCZ012 ∷ []) ⟫ʷ
wn00228 b = lw3 b (Toff012 ∷ K0 ∷ []) (K0 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00229 : Base 3 → ⟪ (CS12 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00229 b = lw3 b (CS12 ∷ K0⁻ ∷ []) (K0⁻ ∷ CS12 ∷ []) tt tt Eq.refl
wn00230 : Base 3 → ⟪ (CS12 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ []) ⟫ʷ
wn00230 b = lw3 b (CS12 ∷ K0 ∷ []) (K0 ∷ CS12 ∷ []) tt tt Eq.refl
wn00231 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00231 b = lw3 b [] (CS02⁻ ∷ CS02 ∷ []) tt tt Eq.refl
wn00232 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ []) ⟫ʷ
wn00232 b = lw3 b [] (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ []) tt tt Eq.refl
wn00233 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn00233 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl
wn00234 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn00234 b = lw0 b (X3 ∷ CS13 ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS13 ∷ X3 ∷ []) tt tt Eq.refl
wn00235 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn00235 b = lw0 b (X3 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) tt tt Eq.refl
wn00236 : Base 3 → ⟪ (S0⁻ ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ S0⁻ ∷ []) ⟫ʷ
wn00236 b = lw3 b (S0⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ S0⁻ ∷ []) tt tt Eq.refl
wn00237 : Base 3 → ⟪ (S0 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ S0 ∷ []) ⟫ʷ
wn00237 b = lw3 b (S0 ∷ CCZ012 ∷ []) (CCZ012 ∷ S0 ∷ []) tt tt Eq.refl
wn00238 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn00238 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn00239 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn00239 b = lw3 b (X2 ∷ CK20⁻ ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn00240 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn00240 b = lw3 b (X2 ∷ CK20 ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl
wn00241 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn00241 b = lw3 b (X2 ∷ CS02 ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl
wn00242 : Base 3 → ⟪ (CS02 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS02 ∷ []) ⟫ʷ
wn00242 b = lw3 b (CS02 ∷ S1 ∷ []) (S1 ∷ CS02 ∷ []) tt tt Eq.refl
wn00243 : Base 3 → ⟪ (CS02 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00243 b = lw3 b (CS02 ∷ S1⁻ ∷ []) (S1⁻ ∷ CS02 ∷ []) tt tt Eq.refl
wn00244 : Base 3 → ⟪ (CS02 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00244 b = lw3 b (CS02 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ []) tt tt Eq.refl
wn00245 : Base 3 → ⟪ (CS02 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS02 ∷ []) ⟫ʷ
wn00245 b = lw3 b (CS02 ∷ CS01 ∷ []) (CS01 ∷ CS02 ∷ []) tt tt Eq.refl
wn00246 : Base 3 → ⟪ (CS02 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00246 b = lw3 b (CS02 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS02 ∷ []) tt tt Eq.refl
wn00247 : Base 3 → ⟪ (Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
wn00247 b = lw3 b (Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) tt tt Eq.refl
wn00248 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn00248 b = lw3 b (X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn00249 : Base 3 → ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn00249 b = lw0 b (X3 ∷ CS13⁻ ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn00250 : Base 3 → ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn00250 b = lw0 b (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn00251 : Base 3 → ⟪ (CCZ012 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ012 ∷ []) ⟫ʷ
wn00251 b = lw3 b (CCZ012 ∷ CS02 ∷ []) (CS02 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00252 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX02 ∷ CX02 ∷ []) ⟫ʷ
wn00252 b = lw3 b [] (CX02 ∷ CX02 ∷ []) tt tt Eq.refl
wn00253 : Base 3 → ⟪ (CX12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX02 ∷ []) ⟫ʷ
wn00253 b = lw3 b (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) tt tt Eq.refl
wn00254 : Base 3 → ⟪ (CCZ012 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00254 b = lw3 b (CCZ012 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00255 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn00255 b = lw0 b (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn00256 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn00256 b = lw0 b (X2 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn00257 : Base 3 → ⟪ (X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ []) ⟫ʷ
wn00257 b = lw0 b (X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ []) tt tt Eq.refl
wn00258 : Base 3 → ⟪ (X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ []) ⟫ʷ
wn00258 b = lw0 b (X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn00259 : Base 3 → ⟪ (CCZ123 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ123 ∷ []) ⟫ʷ
wn00259 b = lw0 b (CCZ123 ∷ CS13 ∷ []) (CS13 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn00260 : Base 3 → ⟪ (CCZ123 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wn00260 b = lw0 b (CCZ123 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl
wn00261 : Base 3 → ⟪ (CX20 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CX20 ∷ []) ⟫ʷ
wn00261 b = lw3 b (CX20 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CX20 ∷ []) tt tt Eq.refl
wn00262 : Base 3 → ⟪ (CS02 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00262 b = lw3 b (CS02 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS02 ∷ []) tt tt Eq.refl
wn00263 : Base 3 → ⟪ (CS02 ∷ S0 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS02⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00263 b = lw3 b (CS02 ∷ S0 ∷ CS02⁻ ∷ []) (S0 ∷ CS02⁻ ∷ CS02 ∷ []) tt tt Eq.refl
wn00264 : Base 3 → ⟪ (CS02⁻ ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00264 b = lw3 b (CS02⁻ ∷ CS01 ∷ []) (CS01 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn00265 : Base 3 → ⟪ (S0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ S0 ∷ []) ⟫ʷ
wn00265 b = lw3 b (S0 ∷ CS01 ∷ []) (CS01 ∷ S0 ∷ []) tt tt Eq.refl
wn00266 : Base 3 → ⟪ (CCZ123 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ123 ∷ []) ⟫ʷ
wn00266 b = lw0 b (CCZ123 ∷ CS23 ∷ []) (CS23 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn00267 : Base 3 → ⟪ (CCZ123 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ123 ∷ []) ⟫ʷ
wn00267 b = lw0 b (CCZ123 ∷ CZ23 ∷ []) (CZ23 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn00268 : Base 3 → ⟪ (S0 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ S0 ∷ []) ⟫ʷ
wn00268 b = lw3 b (S0 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn00269 : Base 3 → ⟪ (CCZ123 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wn00269 b = lw0 b (CCZ123 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl
wn00270 : Base 3 → ⟪ (CS02⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wn00270 b = lw3 b (CS02⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn00271 : Base 3 → ⟪ (K1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K0 ∷ []) ⟫ʷ
wn00271 b = lw3 b (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) tt tt Eq.refl
wn00272 : Base 3 → ⟪ (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ
wn00272 b = lw3 b (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) tt tt Eq.refl
wn00273 : Base 3 → ⟪ (CK21 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK20 ∷ []) ⟫ʷ
wn00273 b = lw3 b (CK21 ∷ Sw01 ∷ []) (Sw01 ∷ CK20 ∷ []) tt tt Eq.refl
wn00274 : Base 3 → ⟪ (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ
wn00274 b = lw3 b (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) tt tt Eq.refl
wn00275 : Base 3 → ⟪ (Sw01 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ Sw01 ∷ []) ⟫ʷ
wn00275 b = lw3 b (Sw01 ∷ CK20 ∷ []) (CK21 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00276 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn00276 b = lw0 b (X3 ∷ CK31 ∷ X3 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) tt tt Eq.refl
wn00277 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn00277 b = lw3 b (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn00278 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn00278 b = lw3 b (X2 ∷ CS12 ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ []) tt tt Eq.refl
wn00279 : Base 3 → ⟪ (CK31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK32 ∷ []) ⟫ʷ
wn00279 b = lw0 b (CK31 ∷ Sw12 ∷ []) (Sw12 ∷ CK32 ∷ []) tt tt Eq.refl
wn00280 : Base 3 → ⟪ (CK32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK31 ∷ []) ⟫ʷ
wn00280 b = lw0 b (CK32 ∷ Sw12 ∷ []) (Sw12 ∷ CK31 ∷ []) tt tt Eq.refl
wn00281 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn00281 b = lw3 b (X2 ∷ CK21 ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ []) tt tt Eq.refl
wn00282 : Base 3 → ⟪ (CK31⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK32⁻ ∷ []) ⟫ʷ
wn00282 b = lw0 b (CK31⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CK32⁻ ∷ []) tt tt Eq.refl
wn00283 : Base 3 → ⟪ (CK32⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK31⁻ ∷ []) ⟫ʷ
wn00283 b = lw0 b (CK32⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CK31⁻ ∷ []) tt tt Eq.refl
wn00284 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn00284 b = lw3 b (X2 ∷ CK21⁻ ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn00285 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn00285 b = lw3 b (X2 ∷ CS12⁻ ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn00286 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ []) ⟫ʷ
wn00286 b = lw3 b (CS02 ∷ CS02 ∷ []) (CS02 ∷ CS02 ∷ []) tt tt Eq.refl
wn00287 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn00287 b = lw0 b (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn00288 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn00288 b = lw0 b (X2 ∷ CS12⁻ ∷ X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn00289 : Base 3 → ⟪ (Toff012 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ Toff012 ∷ []) ⟫ʷ
wn00289 b = lw3 b (Toff012 ∷ S1 ∷ []) (S1 ∷ Toff012 ∷ []) tt tt Eq.refl
wn00290 : Base 3 → ⟪ (Toff012 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ Toff012 ∷ []) ⟫ʷ
wn00290 b = lw3 b (Toff012 ∷ S1⁻ ∷ []) (S1⁻ ∷ Toff012 ∷ []) tt tt Eq.refl
wn00291 : Base 3 → ⟪ (CS02⁻ ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00291 b = lw3 b (CS02⁻ ∷ S1 ∷ []) (S1 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn00292 : Base 3 → ⟪ (CS02⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wn00292 b = lw3 b (CS02⁻ ∷ S1⁻ ∷ []) (S1⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn00293 : Base 3 → ⟪ (Toff102 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff102 ∷ []) ⟫ʷ
wn00293 b = lw3 b (Toff102 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff102 ∷ []) tt tt Eq.refl
wn00294 : Base 3 → ⟪ (S0 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ S0 ∷ []) ⟫ʷ
wn00294 b = lw3 b (S0 ∷ CS12 ∷ []) (CS12 ∷ S0 ∷ []) tt tt Eq.refl
wn00295 : Base 3 → ⟪ (S0 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ S0 ∷ []) ⟫ʷ
wn00295 b = lw3 b (S0 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn00296 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn00296 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn00297 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn00297 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn00298 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn00298 b = lw3 b (X1 ∷ CS01 ∷ X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl
wn00299 : Base 3 → ⟪ (CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
wn00299 b = lw3 b (CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS12 ∷ []) tt tt Eq.refl
wn00300 : Base 3 → ⟪ (CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00300 b = lw3 b (CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00301 : Base 3 → ⟪ (CCZ012 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ012 ∷ []) ⟫ʷ
wn00301 b = lw3 b (CCZ012 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00302 : Base 3 → ⟪ (CS12 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS12 ∷ []) ⟫ʷ
wn00302 b = lw3 b (CS12 ∷ CZ02 ∷ []) (CZ02 ∷ CS12 ∷ []) tt tt Eq.refl
wn00303 : Base 3 → ⟪ (CS12⁻ ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00303 b = lw3 b (CS12⁻ ∷ CZ02 ∷ []) (CZ02 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00304 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn00304 b = lw3 b (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) tt tt Eq.refl
wn00305 : Base 3 → ⟪ (Toff102 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
wn00305 b = lw3 b (Toff102 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ []) tt tt Eq.refl
wn00306 : Base 3 → ⟪ (S1 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S1 ∷ []) ⟫ʷ
wn00306 b = lw0 b (S1 ∷ CS13 ∷ []) (CS13 ∷ S1 ∷ []) tt tt Eq.refl
wn00307 : Base 3 → ⟪ (S1 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S1 ∷ []) ⟫ʷ
wn00307 b = lw0 b (S1 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S1 ∷ []) tt tt Eq.refl
wn00308 : Base 3 → ⟪ (S1⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S1⁻ ∷ []) ⟫ʷ
wn00308 b = lw0 b (S1⁻ ∷ CS13 ∷ []) (CS13 ∷ S1⁻ ∷ []) tt tt Eq.refl
wn00309 : Base 3 → ⟪ (S1⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S1⁻ ∷ []) ⟫ʷ
wn00309 b = lw0 b (S1⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S1⁻ ∷ []) tt tt Eq.refl
wn00310 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wn00310 b = lw3 b (CS02 ∷ CS02 ∷ CS02 ∷ []) (CS02⁻ ∷ []) tt tt Eq.refl
wn00311 : Base 3 → ⟪ (Sw01 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ Sw01 ∷ []) ⟫ʷ
wn00311 b = lw3 b (Sw01 ∷ S0 ∷ []) (S1 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00312 : Base 3 → ⟪ (Sw01 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00312 b = lw3 b (Sw01 ∷ S0⁻ ∷ []) (S1⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00313 : Base 3 → ⟪ (Sw01 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00313 b = lw3 b (Sw01 ∷ K0⁻ ∷ []) (K1⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00314 : Base 3 → ⟪ (Sw01 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ Sw01 ∷ []) ⟫ʷ
wn00314 b = lw3 b (Sw01 ∷ Z0 ∷ []) (Z1 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00315 : Base 3 → ⟪ (Sw01 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ Sw01 ∷ []) ⟫ʷ
wn00315 b = lw3 b (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00316 : Base 3 → ⟪ (Sw01 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00316 b = lw3 b (Sw01 ∷ S1⁻ ∷ []) (S0⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00317 : Base 3 → ⟪ (Sw01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Sw01 ∷ []) ⟫ʷ
wn00317 b = lw3 b (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00318 : Base 3 → ⟪ (Sw01 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ Sw01 ∷ []) ⟫ʷ
wn00318 b = lw3 b (Sw01 ∷ Z1 ∷ []) (Z0 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00319 : Base 3 → ⟪ (Sw01 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00319 b = lw3 b (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00320 : Base 3 → ⟪ (Sw01 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Sw01 ∷ []) ⟫ʷ
wn00320 b = lw3 b (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00321 : Base 3 → ⟪ (Sw01 ∷ CK01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00321 b = lw3 b (Sw01 ∷ CK01⁻ ∷ []) (CK10⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00322 : Base 3 → ⟪ (Sw01 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00322 b = lw3 b (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00323 : Base 3 → ⟪ (Sw01 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Sw01 ∷ []) ⟫ʷ
wn00323 b = lw3 b (Sw01 ∷ CZ02 ∷ []) (CZ12 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00324 : Base 3 → ⟪ (Sw01 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ Sw01 ∷ []) ⟫ʷ
wn00324 b = lw3 b (Sw01 ∷ CK02 ∷ []) (CK12 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00325 : Base 3 → ⟪ (Sw01 ∷ CK02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00325 b = lw3 b (Sw01 ∷ CK02⁻ ∷ []) (CK12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00326 : Base 3 → ⟪ (Sw01 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ Sw01 ∷ []) ⟫ʷ
wn00326 b = lw3 b (Sw01 ∷ CX10 ∷ []) (CX01 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00327 : Base 3 → ⟪ (Sw01 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ Sw01 ∷ []) ⟫ʷ
wn00327 b = lw3 b (Sw01 ∷ CK10 ∷ []) (CK01 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00328 : Base 3 → ⟪ (Sw01 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK01⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00328 b = lw3 b (Sw01 ∷ CK10⁻ ∷ []) (CK01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00329 : Base 3 → ⟪ (Sw01 ∷ CK12 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ Sw01 ∷ []) ⟫ʷ
wn00329 b = lw3 b (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00330 : Base 3 → ⟪ (Sw01 ∷ CK12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK02⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00330 b = lw3 b (Sw01 ∷ CK12⁻ ∷ []) (CK02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00331 : Base 3 → ⟪ (Sw01 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ Sw01 ∷ []) ⟫ʷ
wn00331 b = lw3 b (Sw01 ∷ CX20 ∷ []) (CX21 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00332 : Base 3 → ⟪ (Sw01 ∷ CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00332 b = lw3 b (Sw01 ∷ CK20⁻ ∷ []) (CK21⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00333 : Base 3 → ⟪ (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ
wn00333 b = lw3 b (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) tt tt Eq.refl
wn00334 : Base 3 → ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ
wn00334 b = lw0 b (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) tt tt Eq.refl
wn00335 : Base 3 → ⟪ (Sw23 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sw23 ∷ []) ⟫ʷ
wn00335 b = lw0 b (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00336 : Base 3 → ⟪ (Sw23 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Sw23 ∷ []) ⟫ʷ
wn00336 b = lw0 b (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00337 : Base 3 → ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ
wn00337 b = lw0 b (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) tt tt Eq.refl
wn00338 : Base 3 → ⟪ (Sw12 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ Sw12 ∷ []) ⟫ʷ
wn00338 b = lw3 b (Sw12 ∷ S1 ∷ []) (S2 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00339 : Base 3 → ⟪ (Sw12 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00339 b = lw3 b (Sw12 ∷ S1⁻ ∷ []) (S2⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00340 : Base 3 → ⟪ (Sw12 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Sw12 ∷ []) ⟫ʷ
wn00340 b = lw3 b (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00341 : Base 3 → ⟪ (Sw12 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00341 b = lw3 b (Sw12 ∷ K1⁻ ∷ []) (K2⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00342 : Base 3 → ⟪ (Sw12 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ Sw12 ∷ []) ⟫ʷ
wn00342 b = lw3 b (Sw12 ∷ Z1 ∷ []) (Z2 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00343 : Base 3 → ⟪ (Sw12 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ Sw12 ∷ []) ⟫ʷ
wn00343 b = lw3 b (Sw12 ∷ S2 ∷ []) (S1 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00344 : Base 3 → ⟪ (Sw12 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00344 b = lw3 b (Sw12 ∷ S2⁻ ∷ []) (S1⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00345 : Base 3 → ⟪ (Sw12 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Sw12 ∷ []) ⟫ʷ
wn00345 b = lw3 b (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00346 : Base 3 → ⟪ (Sw12 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00346 b = lw3 b (Sw12 ∷ K2⁻ ∷ []) (K1⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00347 : Base 3 → ⟪ (Sw12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Sw12 ∷ []) ⟫ʷ
wn00347 b = lw3 b (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00348 : Base 3 → ⟪ (Sw12 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ Sw12 ∷ []) ⟫ʷ
wn00348 b = lw3 b (Sw12 ∷ Z2 ∷ []) (Z1 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00349 : Base 3 → ⟪ (Sw12 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Sw12 ∷ []) ⟫ʷ
wn00349 b = lw3 b (Sw12 ∷ CZ12 ∷ []) (CZ12 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00350 : Base 3 → ⟪ (Sw12 ∷ CK12 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ Sw12 ∷ []) ⟫ʷ
wn00350 b = lw3 b (Sw12 ∷ CK12 ∷ []) (CK21 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00351 : Base 3 → ⟪ (Sw12 ∷ CK12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00351 b = lw3 b (Sw12 ∷ CK12⁻ ∷ []) (CK21⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00352 : Base 3 → ⟪ (Sw12 ∷ CK13 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ Sw12 ∷ []) ⟫ʷ
wn00352 b = lw0 b (Sw12 ∷ CK13 ∷ []) (CK23 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00353 : Base 3 → ⟪ (Sw12 ∷ CK13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00353 b = lw0 b (Sw12 ∷ CK13⁻ ∷ []) (CK23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00354 : Base 3 → ⟪ (Sw12 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Sw12 ∷ []) ⟫ʷ
wn00354 b = lw3 b (Sw12 ∷ CX21 ∷ []) (CX12 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00355 : Base 3 → ⟪ (Sw12 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ Sw12 ∷ []) ⟫ʷ
wn00355 b = lw3 b (Sw12 ∷ CK21 ∷ []) (CK12 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00356 : Base 3 → ⟪ (Sw12 ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00356 b = lw3 b (Sw12 ∷ CK21⁻ ∷ []) (CK12⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00357 : Base 3 → ⟪ (Sw12 ∷ CK23 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ Sw12 ∷ []) ⟫ʷ
wn00357 b = lw0 b (Sw12 ∷ CK23 ∷ []) (CK13 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00358 : Base 3 → ⟪ (Sw12 ∷ CK23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK13⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00358 b = lw0 b (Sw12 ∷ CK23⁻ ∷ []) (CK13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00359 : Base 3 → ⟪ (Sw12 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ Sw12 ∷ []) ⟫ʷ
wn00359 b = lw0 b (Sw12 ∷ CK31 ∷ []) (CK32 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00360 : Base 3 → ⟪ (Sw12 ∷ CK31⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00360 b = lw0 b (Sw12 ∷ CK31⁻ ∷ []) (CK32⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00361 : Base 3 → ⟪ (Sw12 ∷ CK32 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ Sw12 ∷ []) ⟫ʷ
wn00361 b = lw0 b (Sw12 ∷ CK32 ∷ []) (CK31 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00362 : Base 3 → ⟪ (Sw12 ∷ CK32⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00362 b = lw0 b (Sw12 ∷ CK32⁻ ∷ []) (CK31⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00363 : Base 3 → ⟪ (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ
wn00363 b = lw3 b (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) tt tt Eq.refl
wn00364 : Base 3 → ⟪ (Sw12 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (ι2 ∷ Sw12 ∷ []) ⟫ʷ
wn00364 b = lw3 b (Sw12 ∷ ι1 ∷ []) (ι2 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00365 : Base 3 → ⟪ (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2 ∷ ι2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ
wn00365 b = lw0 b (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2 ∷ ι2 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) tt tt Eq.refl
wn00366 : Base 3 → ⟪ (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ
wn00366 b = lw3 b (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) tt tt Eq.refl
wn00367 : Base 3 → ⟪ (K1 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K1 ∷ ι2 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ
wn00367 b = lw0 b (K1 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K1 ∷ ι2 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) tt tt Eq.refl
wn00368 : Base 3 → ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ
wn00368 b = lw3 b (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) tt tt Eq.refl
wn00369 : Base 3 → ⟪ (K3 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K3 ∷ ι2 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ
wn00369 b = lw0 b (K3 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K3 ∷ ι2 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) tt tt Eq.refl
wn00370 : Base 3 → ⟪ (Sw23 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00370 b = lw0 b (Sw23 ∷ K2⁻ ∷ []) (K3⁻ ∷ Sw23 ∷ []) tt tt Eq.refl
wn00371 : Base 3 → ⟪ (Sw23 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ Sw23 ∷ []) ⟫ʷ
wn00371 b = lw0 b (Sw23 ∷ Z2 ∷ []) (Z3 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00372 : Base 3 → ⟪ (Sw23 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ Sw23 ∷ []) ⟫ʷ
wn00372 b = lw0 b (Sw23 ∷ S3 ∷ []) (S2 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00373 : Base 3 → ⟪ (Sw23 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00373 b = lw0 b (Sw23 ∷ S3⁻ ∷ []) (S2⁻ ∷ Sw23 ∷ []) tt tt Eq.refl
wn00374 : Base 3 → ⟪ (Sw23 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00374 b = lw0 b (Sw23 ∷ K3⁻ ∷ []) (K2⁻ ∷ Sw23 ∷ []) tt tt Eq.refl
wn00375 : Base 3 → ⟪ (Sw23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Sw23 ∷ []) ⟫ʷ
wn00375 b = lw0 b (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00376 : Base 3 → ⟪ (Sw23 ∷ Z3 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ Sw23 ∷ []) ⟫ʷ
wn00376 b = lw0 b (Sw23 ∷ Z3 ∷ []) (Z2 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00377 : Base 3 → ⟪ (Sw23 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ Sw23 ∷ []) ⟫ʷ
wn00377 b = lw0 b (Sw23 ∷ CZ23 ∷ []) (CZ23 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00378 : Base 3 → ⟪ (Sw23 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ Sw23 ∷ []) ⟫ʷ
wn00378 b = lw0 b (Sw23 ∷ CX23 ∷ []) (CX32 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00379 : Base 3 → ⟪ (Sw23 ∷ CK23 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ Sw23 ∷ []) ⟫ʷ
wn00379 b = lw0 b (Sw23 ∷ CK23 ∷ []) (CK32 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00380 : Base 3 → ⟪ (Sw23 ∷ CK23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00380 b = lw0 b (Sw23 ∷ CK23⁻ ∷ []) (CK32⁻ ∷ Sw23 ∷ []) tt tt Eq.refl
wn00381 : Base 3 → ⟪ (Sw23 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Sw23 ∷ []) ⟫ʷ
wn00381 b = lw0 b (Sw23 ∷ CX32 ∷ []) (CX23 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00382 : Base 3 → ⟪ (Sw23 ∷ CK32 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ Sw23 ∷ []) ⟫ʷ
wn00382 b = lw0 b (Sw23 ∷ CK32 ∷ []) (CK23 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00383 : Base 3 → ⟪ (Sw23 ∷ CK32⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00383 b = lw0 b (Sw23 ∷ CK32⁻ ∷ []) (CK23⁻ ∷ Sw23 ∷ []) tt tt Eq.refl
wn00384 : Base 3 → ⟪ (K1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ
wn00384 b = lw0 b (K1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) tt tt Eq.refl
wn00385 : Base 3 → ⟪ (K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ
wn00385 b = lw0 b (K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K3 ∷ ι1 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) tt tt Eq.refl
wn00386 : Base 3 → ⟪ (K2 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ
wn00386 b = lw0 b (K2 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) tt tt Eq.refl
wn00387 : Base 3 → ⟪ (X0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00387 b = lw3 b (X0 ∷ X0 ∷ []) [] tt tt Eq.refl
wn00388 : Base 3 → ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00388 b = lw3 b (X1 ∷ X1 ∷ []) [] tt tt Eq.refl
wn00389 : Base 3 → ⟪ (X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00389 b = lw3 b (X2 ∷ X2 ∷ []) [] tt tt Eq.refl
wn00390 : Base 3 → ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00390 b = lw0 b (X3 ∷ X3 ∷ []) [] tt tt Eq.refl
wn00391 : Base 3 → ⟪ (X0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn00391 b = lw3 b (X0 ∷ S0 ∷ K0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) tt tt Eq.refl
wn00392 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ
wn00392 b = lw3 b (K0⁻ ∷ S0⁻ ∷ X0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) tt tt Eq.refl
wn00393 : Base 3 → ⟪ (X2 ∷ S2 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ
wn00393 b = lw3 b (X2 ∷ S2 ∷ K2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) tt tt Eq.refl
wn00394 : Base 3 → ⟪ (K2⁻ ∷ S2⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ
wn00394 b = lw3 b (K2⁻ ∷ S2⁻ ∷ X2 ∷ []) (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) tt tt Eq.refl
wn00395 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn00395 b = lw0 b (X3 ∷ CS23 ∷ X3 ∷ Toff213 ∷ []) (Toff213 ∷ X3 ∷ CS23 ∷ X3 ∷ []) tt tt Eq.refl
wn00396 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn00396 b = lw0 b (X3 ∷ CS23 ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ []) tt tt Eq.refl
wn00397 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn00397 b = lw0 b (X3 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) tt tt Eq.refl
wn00398 : Base 3 → ⟪ (K2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ K1 ∷ []) ⟫ʷ
wn00398 b = lw3 b (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) tt tt Eq.refl
wn00399 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn00399 b = lw0 b (X3 ∷ CK32 ∷ X3 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) tt tt Eq.refl
wn00400 : Base 3 → ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn00400 b = lw0 b (X3 ∷ CS23⁻ ∷ X3 ∷ Toff213 ∷ []) (Toff213 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn00401 : Base 3 → ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn00401 b = lw0 b (X3 ∷ CS23⁻ ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn00402 : Base 3 → ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn00402 b = lw0 b (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn00403 : Base 3 → ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn00403 b = lw0 b (X3 ∷ CS23⁻ ∷ X3 ∷ Toff123 ∷ []) (Toff123 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn00404 : Base 3 → ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn00404 b = lw0 b (X3 ∷ CK32⁻ ∷ X3 ∷ Toff123 ∷ []) (Toff123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn00405 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn00405 b = lw0 b (X3 ∷ CS23 ∷ X3 ∷ Toff123 ∷ []) (Toff123 ∷ X3 ∷ CS23 ∷ X3 ∷ []) tt tt Eq.refl
wn00406 : Base 3 → ⟪ (CS12 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CS12 ∷ []) ⟫ʷ
wn00406 b = lw0 b (CS12 ∷ CS23 ∷ []) (CS23 ∷ CS12 ∷ []) tt tt Eq.refl
wn00407 : Base 3 → ⟪ (CX21 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX21 ∷ []) ⟫ʷ
wn00407 b = lw0 b (CX21 ∷ CS23 ∷ []) (CS23 ∷ CX21 ∷ []) tt tt Eq.refl
wn00408 : Base 3 → ⟪ (CS23 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS23 ∷ []) ⟫ʷ
wn00408 b = lw1 b (CS23 ∷ S0 ∷ []) (S0 ∷ CS23 ∷ []) tt tt Eq.refl

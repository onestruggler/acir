------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL02 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl0245 : Complete 4 → ⟪ (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0245 c4 = lw4 c4 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl

wl0246 : Complete 4 → ⟪ (CS02 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0246 c4 = lw4 c4 (CS02 ∷ CS02⁻ ∷ []) [] tt tt Eq.refl

wl0247 : Complete 4 → ⟪ (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0247 c4 = lw4 c4 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] tt tt Eq.refl

wl0248 : Complete 4 → ⟪ (Toff314 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0248 c4 = lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl

wl0249 : Complete 4 → ⟪ (CS03⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0249 c4 = lw4 c4 (CS03⁻ ∷ CS03 ∷ []) [] tt tt Eq.refl

wl0250 : Complete 4 → ⟪ (CS03 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0250 c4 = lw4 c4 (CS03 ∷ CS03⁻ ∷ []) [] tt tt Eq.refl

wl0251 : Complete 4 → ⟪ (CX01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX10 ∷ []) ⟫ʷ
wl0251 c4 = lw4 c4 (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) tt tt Eq.refl

wl0252 : Complete 4 → ⟪ (CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ []) ⟫ʷ
wl0252 c4 = lw4 c4 (CZ01 ∷ []) (CZ01 ∷ []) tt tt Eq.refl

wl0253 : Complete 4 → ⟪ (CZ02 ∷ CX20 ∷ Toff012 ∷ CCZ012 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ
wl0253 c4 = lw4 c4 (CZ02 ∷ CX20 ∷ Toff012 ∷ CCZ012 ∷ X1 ∷ []) (X1 ∷ CCZ012 ∷ Toff012 ∷ []) tt tt Eq.refl

wl0254 : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ CX20 ∷ CZ02 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
wl0254 c4 = lw4 c4 (CCZ012 ∷ Toff012 ∷ CX20 ∷ CZ02 ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0255 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
wl0255 c4 = lw0 c4 (CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl

wl0256 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
wl0256 c4 = lw4 c4 (CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl

wl0257 : Complete 4 → ⟪ (K0⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K1⁻ ∷ []) ⟫ʷ
wl0257 c4 = lw4 c4 (K0⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0258 : Complete 4 → ⟪ (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ []) ⟫ʷ
wl0258 c4 = lw4 c4 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) tt tt Eq.refl

wl0259 : Complete 4 → ⟪ (K1⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ K1⁻ ∷ []) ⟫ʷ
wl0259 c4 = lw4 c4 (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0260 : Complete 4 → ⟪ (K1⁻ ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0260 c4 = lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl

wl0261 : Complete 4 → ⟪ (CCZ012 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ
wl0261 c4 = lw4 c4 (CCZ012 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0262 : Complete 4 → ⟪ (CCZ123 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ123 ∷ []) ⟫ʷ
wl0262 c4 = lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0263 : Complete 4 → ⟪ (Toff023 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0263 c4 = lw4 c4 (Toff023 ∷ Toff023 ∷ []) [] tt tt Eq.refl

wl0264 : Complete 4 → ⟪ (CCZ123 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ123 ∷ []) ⟫ʷ
wl0264 c4 = lw0 c4 (CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0265 : Complete 4 → ⟪ (CCZ234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0265 c4 = lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl

wl0266 : Complete 4 → ⟪ (K1 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ K1 ∷ []) ⟫ʷ
wl0266 c4 = lw4 c4 (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) tt tt Eq.refl

wl0267 : Complete 4 → ⟪ (Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ []) ⟫ʷ
wl0267 c4 = lw0 c4 (Toff314 ∷ []) (Toff314 ∷ []) tt tt Eq.refl

wl0268 : Complete 4 → ⟪ (Toff201 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0268 c4 = lw4 c4 (Toff201 ∷ Toff201 ∷ []) [] tt tt Eq.refl

wl0269 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wl0269 c4 = lw4 c4 (CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl

wl0270 : Complete 4 → ⟪ (CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
wl0270 c4 = lw4 c4 (CS12 ∷ []) (CS12 ∷ []) tt tt Eq.refl

wl0271 : Complete 4 → ⟪ (CS12 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS12 ∷ []) ⟫ʷ
wl0271 c4 = lw0 c4 (CS12 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS12 ∷ []) tt tt Eq.refl

wl0272 : Complete 4 → ⟪ (CS12 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS12 ∷ []) ⟫ʷ
wl0272 c4 = lw0 c4 (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) tt tt Eq.refl

wl0273 : Complete 4 → ⟪ (CS12 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS12 ∷ []) ⟫ʷ
wl0273 c4 = lw0 c4 (CS12 ∷ CS14 ∷ []) (CS14 ∷ CS12 ∷ []) tt tt Eq.refl

wl0274 : Complete 4 → ⟪ (CS14⁻ ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0274 c4 = lw0 c4 (CS14⁻ ∷ CS23 ∷ []) (CS23 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0275 : Complete 4 → ⟪ (CS23 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS23 ∷ []) ⟫ʷ
wl0275 c4 = lw0 c4 (CS23 ∷ Toff423 ∷ []) (Toff423 ∷ CS23 ∷ []) tt tt Eq.refl

wl0276 : Complete 4 → ⟪ (CS14 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CS14 ∷ []) ⟫ʷ
wl0276 c4 = lw0 c4 (CS14 ∷ CS23 ∷ []) (CS23 ∷ CS14 ∷ []) tt tt Eq.refl

wl0277 : Complete 4 → ⟪ (CX23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX32 ∷ []) ⟫ʷ
wl0277 c4 = lw4 c4 (CX23 ∷ Sw23 ∷ []) (Sw23 ∷ CX32 ∷ []) tt tt Eq.refl

wl0278 : Complete 4 → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wl0278 c4 = lw0 c4 (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wl0279 : Complete 4 → ⟪ (CX41 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0279 c4 = lw0 c4 (CX41 ∷ CX41 ∷ []) [] tt tt Eq.refl

wl0280 : Complete 4 → ⟪ (Sw12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Sw12 ∷ []) ⟫ʷ
wl0280 c4 = lw4 c4 (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0281 : Complete 4 → ⟪ (Sw23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Sw23 ∷ []) ⟫ʷ
wl0281 c4 = lw4 c4 (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0282 : Complete 4 → ⟪ (Sw34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Sw34 ∷ []) ⟫ʷ
wl0282 c4 = lw0 c4 (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) tt tt Eq.refl

wl0283 : Complete 4 → ⟪ (X4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0283 c4 = lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl

wl0284 : Complete 4 → ⟪ (CCZ023 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wl0284 c4 = lw4 c4 (CCZ023 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0285 : Complete 4 → ⟪ (CS12⁻ ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0285 c4 = lw0 c4 (CS12⁻ ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ []) (Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0286 : Complete 4 → ⟪ (CS12⁻ ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wl0286 c4 = lw4 c4 (CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0287 : Complete 4 → ⟪ (CS12 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS12 ∷ []) ⟫ʷ
wl0287 c4 = lw4 c4 (CS12 ∷ K0⁻ ∷ []) (K0⁻ ∷ CS12 ∷ []) tt tt Eq.refl

wl0288 : Complete 4 → ⟪ (CS12⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wl0288 c4 = lw4 c4 (CS12⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0289 : Complete 4 → ⟪ (CS01 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS01 ∷ []) ⟫ʷ
wl0289 c4 = lw4 c4 (CS01 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS01 ∷ []) tt tt Eq.refl

wl0290 : Complete 4 → ⟪ (CS12 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ []) ⟫ʷ
wl0290 c4 = lw4 c4 (CS12 ∷ K0 ∷ []) (K0 ∷ CS12 ∷ []) tt tt Eq.refl

wl0291 : Complete 4 → ⟪ (CS12⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0291 c4 = lw4 c4 (CS12⁻ ∷ K0 ∷ []) (K0 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0292 : Complete 4 → ⟪ (CCZ023 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ023 ∷ []) ⟫ʷ
wl0292 c4 = lw4 c4 (CCZ023 ∷ CS12 ∷ []) (CS12 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0293 : Complete 4 → ⟪ (CS12 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CS12 ∷ Toff234 ∷ CS12 ∷ []) ⟫ʷ
wl0293 c4 = lw0 c4 (CS12 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ []) (Toff234 ∷ CS12 ∷ Toff234 ∷ CS12 ∷ []) tt tt Eq.refl

wl0294 : Complete 4 → ⟪ (CS12 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS12 ∷ []) ⟫ʷ
wl0294 c4 = lw4 c4 (CS12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12 ∷ []) tt tt Eq.refl

wl0295 : Complete 4 → ⟪ (CCZ123 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ123 ∷ []) ⟫ʷ
wl0295 c4 = lw0 c4 (CCZ123 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0296 : Complete 4 → ⟪ (Toff423 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0296 c4 = lw0 c4 (Toff423 ∷ Toff423 ∷ []) [] tt tt Eq.refl

wl0297 : Complete 4 → ⟪ (CCZ123 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ123 ∷ []) ⟫ʷ
wl0297 c4 = lw0 c4 (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0298 : Complete 4 → ⟪ (CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ []) ⟫ʷ
wl0298 c4 = lw0 c4 (CS14 ∷ []) (CS14 ∷ []) tt tt Eq.refl

wl0299 : Complete 4 → ⟪ (CS14 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS14 ∷ []) ⟫ʷ
wl0299 c4 = lw0 c4 (CS14 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS14 ∷ []) tt tt Eq.refl

wl0300 : Complete 4 → ⟪ (CS14 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14 ∷ []) ⟫ʷ
wl0300 c4 = lw0 c4 (CS14 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14 ∷ []) tt tt Eq.refl

wl0301 : Complete 4 → ⟪ (CS01⁻ ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0301 c4 = lw2 c4 (CS01⁻ ∷ K4 ∷ []) (K4 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0302 : Complete 4 → ⟪ (CS01 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ CS01 ∷ []) ⟫ʷ
wl0302 c4 = lw2 c4 (CS01 ∷ K4 ∷ []) (K4 ∷ CS01 ∷ []) tt tt Eq.refl

wl0303 : Complete 4 → ⟪ (CS14⁻ ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0303 c4 = lw0 c4 (CS14⁻ ∷ CS24 ∷ []) (CS24 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0304 : Complete 4 → ⟪ (CS24 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14 ∷ Toff423 ∷ CS24 ∷ []) ⟫ʷ
wl0304 c4 = lw0 c4 (CS24 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS24 ∷ []) tt tt Eq.refl

wl0305 : Complete 4 → ⟪ (CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ []) ⟫ʷ
wl0305 c4 = lw0 c4 (CS24 ∷ CS24 ∷ []) (CZ24 ∷ []) tt tt Eq.refl

wl0306 : Complete 4 → ⟪ (K1⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K0⁻ ∷ []) ⟫ʷ
wl0306 c4 = lw4 c4 (K1⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K0⁻ ∷ []) tt tt Eq.refl

wl0307 : Complete 4 → ⟪ (K1⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ K2⁻ ∷ []) ⟫ʷ
wl0307 c4 = lw4 c4 (K1⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0308 : Complete 4 → ⟪ (K2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ K1⁻ ∷ []) ⟫ʷ
wl0308 c4 = lw4 c4 (K2⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl0309 : Complete 4 → ⟪ (K2⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ K3⁻ ∷ []) ⟫ʷ
wl0309 c4 = lw4 c4 (K2⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0310 : Complete 4 → ⟪ (K3⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ K2⁻ ∷ []) ⟫ʷ
wl0310 c4 = lw4 c4 (K3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl0311 : Complete 4 → ⟪ (K3⁻ ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ K4⁻ ∷ []) ⟫ʷ
wl0311 c4 = lw0 c4 (K3⁻ ∷ Sw34 ∷ []) (Sw34 ∷ K4⁻ ∷ []) tt tt Eq.refl

wl0312 : Complete 4 → ⟪ (K4⁻ ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ K3⁻ ∷ []) ⟫ʷ
wl0312 c4 = lw0 c4 (K4⁻ ∷ Sw34 ∷ []) (Sw34 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0313 : Complete 4 → ⟪ (CS01⁻ ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wl0313 c4 = lw2 c4 (CS01⁻ ∷ K4⁻ ∷ []) (K4⁻ ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0314 : Complete 4 → ⟪ (CS01 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ CS01 ∷ []) ⟫ʷ
wl0314 c4 = lw2 c4 (CS01 ∷ K4⁻ ∷ []) (K4⁻ ∷ CS01 ∷ []) tt tt Eq.refl

wl0315 : Complete 4 → ⟪ (CX34 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ CZ34 ∷ K4⁻ ∷ []) ⟫ʷ
wl0315 c4 = lw0 c4 (CX34 ∷ []) (K4 ∷ CZ34 ∷ K4⁻ ∷ []) tt tt Eq.refl

wl0316 : Complete 4 → ⟪ (CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ []) ⟫ʷ
wl0316 c4 = lw0 c4 (CS14⁻ ∷ []) (CS14⁻ ∷ []) tt tt Eq.refl

wl0317 : Complete 4 → ⟪ (CS14⁻ ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS14⁻ ∷ []) ⟫ʷ
wl0317 c4 = lw0 c4 (CS14⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0318 : Complete 4 → ⟪ (CS14⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0318 c4 = lw0 c4 (CS14⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0319 : Complete 4 → ⟪ (CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
wl0319 c4 = lw4 c4 (CS13 ∷ []) (CS13 ∷ []) tt tt Eq.refl

wl0320 : Complete 4 → ⟪ (CS13 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS13 ∷ []) ⟫ʷ
wl0320 c4 = lw0 c4 (CS13 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS13 ∷ []) tt tt Eq.refl

wl0321 : Complete 4 → ⟪ (CS13 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS13 ∷ []) ⟫ʷ
wl0321 c4 = lw0 c4 (CS13 ∷ Toff423 ∷ []) (Toff423 ∷ CS13 ∷ []) tt tt Eq.refl

wl0322 : Complete 4 → ⟪ (CS13 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS13 ∷ []) ⟫ʷ
wl0322 c4 = lw0 c4 (CS13 ∷ CS14 ∷ []) (CS14 ∷ CS13 ∷ []) tt tt Eq.refl

wl0323 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) ⟫ʷ
wl0323 c4 = lw0 c4 (CCZ124 ∷ []) (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) tt tt Eq.refl

wl0324 : Complete 4 → ⟪ (CS01 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0324 c4 = lw4 c4 (CS01 ∷ CS01⁻ ∷ []) [] tt tt Eq.refl

wl0325 : Complete 4 → ⟪ (CS14 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS14 ∷ []) ⟫ʷ
wl0325 c4 = lw0 c4 (CS14 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS14 ∷ []) tt tt Eq.refl

wl0326 : Complete 4 → ⟪ (CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS14 ∷ []) ⟫ʷ
wl0326 c4 = lw0 c4 (CS14 ∷ CS14 ∷ []) (CS14 ∷ CS14 ∷ []) tt tt Eq.refl

wl0327 : Complete 4 → ⟪ (CS24 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS24 ∷ []) ⟫ʷ
wl0327 c4 = lw0 c4 (CS24 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS24 ∷ []) tt tt Eq.refl

wl0328 : Complete 4 → ⟪ (CS14 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS14 ∷ []) ⟫ʷ
wl0328 c4 = lw0 c4 (CS14 ∷ CS24 ∷ []) (CS24 ∷ CS14 ∷ []) tt tt Eq.refl

wl0329 : Complete 4 → ⟪ (CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0329 c4 = lw0 c4 (CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0330 : Complete 4 → ⟪ (K0 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ K0 ∷ []) ⟫ʷ
wl0330 c4 = lw1 c4 (K0 ∷ Toff423 ∷ []) (Toff423 ∷ K0 ∷ []) tt tt Eq.refl

wl0331 : Complete 4 → ⟪ (CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
wl0331 c4 = lw4 c4 (CS02 ∷ []) (CS02 ∷ []) tt tt Eq.refl

wl0332 : Complete 4 → ⟪ (CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
wl0332 c4 = lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl

wl0333 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) ⟫ʷ
wl0333 c4 = lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl

wl0334 : Complete 4 → ⟪ (CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) ⟫ʷ
wl0334 c4 = lw4 c4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff013 ∷ []) (Toff013 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) tt tt Eq.refl

wl0335 : Complete 4 → ⟪ (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ []) ⟫ʷ
wl0335 c4 = lw0 c4 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) tt tt Eq.refl

wl0336 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) ⟫ʷ
wl0336 c4 = lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) tt tt Eq.refl

wl0337 : Complete 4 → ⟪ (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) ⟫ʷ
wl0337 c4 = lw4 c4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) tt tt Eq.refl

wl0338 : Complete 4 → ⟪ (CS24⁻ ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0338 c4 = lw0 c4 (CS24⁻ ∷ CX13 ∷ []) (CX13 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0339 : Complete 4 → ⟪ (CS24 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CS24 ∷ []) ⟫ʷ
wl0339 c4 = lw0 c4 (CS24 ∷ CX13 ∷ []) (CX13 ∷ CS24 ∷ []) tt tt Eq.refl

wl0340 : Complete 4 → ⟪ (K0⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ K0⁻ ∷ []) ⟫ʷ
wl0340 c4 = lw1 c4 (K0⁻ ∷ Toff423 ∷ []) (Toff423 ∷ K0⁻ ∷ []) tt tt Eq.refl

wl0341 : Complete 4 → ⟪ (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wl0341 c4 = lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl

wl0342 : Complete 4 → ⟪ (CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
wl0342 c4 = lw4 c4 (CS03 ∷ []) (CS03 ∷ []) tt tt Eq.refl

wl0343 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wl0343 c4 = lw0 c4 (CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wl0344 : Complete 4 → ⟪ (CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ []) ⟫ʷ
wl0344 c4 = lw0 c4 (CS34 ∷ []) (CS34 ∷ []) tt tt Eq.refl

wl0345 : Complete 4 → ⟪ (CS14⁻ ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0345 c4 = lw0 c4 (CS14⁻ ∷ CS34 ∷ []) (CS34 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0346 : Complete 4 → ⟪ (CS34 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14 ∷ Toff423 ∷ CS34 ∷ []) ⟫ʷ
wl0346 c4 = lw0 c4 (CS34 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS34 ∷ []) tt tt Eq.refl

wl0347 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wl0347 c4 = lw0 c4 (CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wl0348 : Complete 4 → ⟪ (CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wl0348 c4 = lw4 c4 (CS02⁻ ∷ []) (CS02⁻ ∷ []) tt tt Eq.refl

wl0349 : Complete 4 → ⟪ (CX13 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0349 c4 = lw4 c4 (CX13 ∷ CX13 ∷ []) [] tt tt Eq.refl

wl0350 : Complete 4 → ⟪ (CCZ124 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ124 ∷ []) ⟫ʷ
wl0350 c4 = lw0 c4 (CCZ124 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0351 : Complete 4 → ⟪ (CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0351 c4 = lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl

wl0352 : Complete 4 → ⟪ (CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ []) ⟫ʷ
wl0352 c4 = lw0 c4 (CS24 ∷ []) (CS24 ∷ []) tt tt Eq.refl

wl0353 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) ⟫ʷ
wl0353 c4 = lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) tt tt Eq.refl

wl0354 : Complete 4 → ⟪ (CS14⁻ ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0354 c4 = lw0 c4 (CS14⁻ ∷ CX23 ∷ []) (CX23 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0355 : Complete 4 → ⟪ (CS14 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CS14 ∷ []) ⟫ʷ
wl0355 c4 = lw0 c4 (CS14 ∷ CX23 ∷ []) (CX23 ∷ CS14 ∷ []) tt tt Eq.refl

wl0356 : Complete 4 → ⟪ (CCZ124 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ124 ∷ []) ⟫ʷ
wl0356 c4 = lw0 c4 (CCZ124 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0357 : Complete 4 → ⟪ (CCZ123 ∷ Toff423 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl0357 c4 = lw0 c4 (CCZ123 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0358 : Complete 4 → ⟪ (CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl0358 c4 = lw0 c4 (CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0359 : Complete 4 → ⟪ (CCZ012 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wl0359 c4 = lw4 c4 (CCZ012 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0360 : Complete 4 → ⟪ (CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
wl0360 c4 = lw4 c4 (CS01⁻ ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl

wl0361 : Complete 4 → ⟪ (S0⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ S0⁻ ∷ []) ⟫ʷ
wl0361 c4 = lw4 c4 (S0⁻ ∷ Toff102 ∷ []) (Toff102 ∷ S0⁻ ∷ []) tt tt Eq.refl

wl0362 : Complete 4 → ⟪ (CS24 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS24 ∷ []) ⟫ʷ
wl0362 c4 = lw1 c4 (CS24 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS24 ∷ []) tt tt Eq.refl

wl0363 : Complete 4 → ⟪ (CS24⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS24⁻ ∷ []) ⟫ʷ
wl0363 c4 = lw1 c4 (CS24⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0364 : Complete 4 → ⟪ (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
wl0364 c4 = lw0 c4 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl

wl0365 : Complete 4 → ⟪ (K3 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ K3 ∷ []) ⟫ʷ
wl0365 c4 = lw4 c4 (K3 ∷ Toff012 ∷ []) (Toff012 ∷ K3 ∷ []) tt tt Eq.refl

wl0366 : Complete 4 → ⟪ (K3⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ K3⁻ ∷ []) ⟫ʷ
wl0366 c4 = lw4 c4 (K3⁻ ∷ Toff012 ∷ []) (Toff012 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0367 : Complete 4 → ⟪ (Sw34 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sw34 ∷ []) ⟫ʷ
wl0367 c4 = lw0 c4 (Sw34 ∷ X3 ∷ []) (X4 ∷ Sw34 ∷ []) tt tt Eq.refl

wl0368 : Complete 4 → ⟪ (Sw23 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Sw23 ∷ []) ⟫ʷ
wl0368 c4 = lw4 c4 (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0369 : Complete 4 → ⟪ (Sw12 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Sw12 ∷ []) ⟫ʷ
wl0369 c4 = lw4 c4 (Sw12 ∷ X1 ∷ []) (X2 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0370 : Complete 4 → ⟪ (Sw01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Sw01 ∷ []) ⟫ʷ
wl0370 c4 = lw4 c4 (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) tt tt Eq.refl

wl0371 : Complete 4 → ⟪ (Sw01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Sw01 ∷ []) ⟫ʷ
wl0371 c4 = lw4 c4 (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) tt tt Eq.refl

wl0372 : Complete 4 → ⟪ (S0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S1 ∷ []) ⟫ʷ
wl0372 c4 = lw4 c4 (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) tt tt Eq.refl

wl0373 : Complete 4 → ⟪ (S1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S0 ∷ []) ⟫ʷ
wl0373 c4 = lw4 c4 (S1 ∷ Sw01 ∷ []) (Sw01 ∷ S0 ∷ []) tt tt Eq.refl

wl0374 : Complete 4 → ⟪ (X1 ∷ S1 ∷ X1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ []) ⟫ʷ
wl0374 c4 = lw4 c4 (X1 ∷ S1 ∷ X1 ∷ S1 ∷ []) (ι ∷ []) tt tt Eq.refl

wl0375 : Complete 4 → ⟪ (CS14⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (S4⁻ ∷ []) ⟫ʷ
wl0375 c4 = lw0 c4 (CS14⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (S4⁻ ∷ []) tt tt Eq.refl

wl0376 : Complete 4 → ⟪ (K0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ []) ⟫ʷ
wl0376 c4 = lw4 c4 (K0 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ []) tt tt Eq.refl

wl0377 : Complete 4 → ⟪ (CS14⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14⁻ ∷ X1 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0377 c4 = lw0 c4 (CS14⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0378 : Complete 4 → ⟪ (S1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ []) ⟫ʷ
wl0378 c4 = lw0 c4 (S1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ []) tt tt Eq.refl

wl0379 : Complete 4 → ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0379 c4 = lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl

wl0380 : Complete 4 → ⟪ (CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ123 ∷ X1 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0380 c4 = lw0 c4 (CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0381 : Complete 4 → ⟪ (CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff314 ∷ X1 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0381 c4 = lw0 c4 (CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0382 : Complete 4 → ⟪ (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ []) ⟫ʷ
wl0382 c4 = lw4 c4 (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ []) tt tt Eq.refl

wl0383 : Complete 4 → ⟪ (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ []) ⟫ʷ
wl0383 c4 = lw0 c4 (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ []) tt tt Eq.refl

wl0384 : Complete 4 → ⟪ (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03 ∷ X1 ∷ S1 ∷ []) ⟫ʷ
wl0384 c4 = lw4 c4 (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1 ∷ []) tt tt Eq.refl

wl0385 : Complete 4 → ⟪ (S1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03⁻ ∷ X1 ∷ S1 ∷ []) ⟫ʷ
wl0385 c4 = lw4 c4 (S1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1 ∷ []) tt tt Eq.refl

wl0386 : Complete 4 → ⟪ (Toff201 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ Toff201 ∷ []) ⟫ʷ
wl0386 c4 = lw4 c4 (Toff201 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff201 ∷ []) tt tt Eq.refl

wl0387 : Complete 4 → ⟪ (S1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ S1 ∷ []) ⟫ʷ
wl0387 c4 = lw4 c4 (S1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ S1 ∷ []) tt tt Eq.refl

wl0388 : Complete 4 → ⟪ (CK10 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ []) ⟫ʷ
wl0388 c4 = lw4 c4 (CK10 ∷ []) (ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ []) tt tt Eq.refl

wl0389 : Complete 4 → ⟪ (CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) ⟫ʷ
wl0389 c4 = lw4 c4 (CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl

wl0390 : Complete 4 → ⟪ (CS01 ∷ X1 ∷ CS03 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) ⟫ʷ
wl0390 c4 = lw4 c4 (CS01 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl

wl0391 : Complete 4 → ⟪ (CS01 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) ⟫ʷ
wl0391 c4 = lw4 c4 (CS01 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl

wl0392 : Complete 4 → ⟪ (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) ⟫ʷ
wl0392 c4 = lw4 c4 (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) tt tt Eq.refl

wl0393 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) ⟫ʷ
wl0393 c4 = lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) tt tt Eq.refl

wl0394 : Complete 4 → ⟪ (CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) ⟫ʷ
wl0394 c4 = lw4 c4 (CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl

wl0395 : Complete 4 → ⟪ (CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) ⟫ʷ
wl0395 c4 = lw2 c4 (CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl

wl0396 : Complete 4 → ⟪ (CS01 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) ⟫ʷ
wl0396 c4 = lw4 c4 (CS01 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl

wl0397 : Complete 4 → ⟪ (S1⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) ⟫ʷ
wl0397 c4 = lw4 c4 (S1⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl

wl0398 : Complete 4 → ⟪ (S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) ⟫ʷ
wl0398 c4 = lw0 c4 (S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl

wl0399 : Complete 4 → ⟪ (S1⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03 ∷ X1 ∷ S1⁻ ∷ []) ⟫ʷ
wl0399 c4 = lw4 c4 (S1⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl

wl0400 : Complete 4 → ⟪ (S1⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03⁻ ∷ X1 ∷ S1⁻ ∷ []) ⟫ʷ
wl0400 c4 = lw4 c4 (S1⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl

wl0401 : Complete 4 → ⟪ (CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0401 c4 = lw4 c4 (CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0402 : Complete 4 → ⟪ (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ []) ⟫ʷ
wl0402 c4 = lw0 c4 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl

wl0403 : Complete 4 → ⟪ (K3⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ K3⁻ ∷ []) ⟫ʷ
wl0403 c4 = lw4 c4 (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0404 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) ⟫ʷ
wl0404 c4 = lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) tt tt Eq.refl

wl0405 : Complete 4 → ⟪ (CS34 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS34 ∷ []) ⟫ʷ
wl0405 c4 = lw0 c4 (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) tt tt Eq.refl

wl0406 : Complete 4 → ⟪ (CX41 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CX41 ∷ []) ⟫ʷ
wl0406 c4 = lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl

wl0407 : Complete 4 → ⟪ (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0407 c4 = lw4 c4 (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0408 : Complete 4 → ⟪ (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) ⟫ʷ
wl0408 c4 = lw0 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl

wl0409 : Complete 4 → ⟪ (CS13 ∷ X1 ∷ K2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ K2 ∷ X1 ∷ CS13 ∷ []) ⟫ʷ
wl0409 c4 = lw4 c4 (CS13 ∷ X1 ∷ K2 ∷ X1 ∷ []) (X1 ∷ K2 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl

wl0410 : Complete 4 → ⟪ (CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS24 ∷ X1 ∷ CS13 ∷ []) ⟫ʷ
wl0410 c4 = lw0 c4 (CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl

wl0411 : Complete 4 → ⟪ (CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS24⁻ ∷ X1 ∷ CS13 ∷ []) ⟫ʷ
wl0411 c4 = lw0 c4 (CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl

wl0412 : Complete 4 → ⟪ (CS13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ []) ⟫ʷ
wl0412 c4 = lw4 c4 (CS13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl

wl0413 : Complete 4 → ⟪ (CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ []) ⟫ʷ
wl0413 c4 = lw4 c4 (CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ []) (X1 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl

wl0414 : Complete 4 → ⟪ (CS13 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ []) ⟫ʷ
wl0414 c4 = lw4 c4 (CS13 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl

wl0415 : Complete 4 → ⟪ (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) ⟫ʷ
wl0415 c4 = lw0 c4 (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl

wl0416 : Complete 4 → ⟪ (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) ⟫ʷ
wl0416 c4 = lw4 c4 (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl

wl0417 : Complete 4 → ⟪ (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) ⟫ʷ
wl0417 c4 = lw4 c4 (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl

wl0418 : Complete 4 → ⟪ (K3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ K3 ∷ []) ⟫ʷ
wl0418 c4 = lw4 c4 (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) tt tt Eq.refl

wl0419 : Complete 4 → ⟪ (CS03 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03 ∷ []) ⟫ʷ
wl0419 c4 = lw4 c4 (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) tt tt Eq.refl

wl0420 : Complete 4 → ⟪ (CK10 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ []) ⟫ʷ
wl0420 c4 = lw4 c4 (CK10 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ []) tt tt Eq.refl

wl0421 : Complete 4 → ⟪ (CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ []) ⟫ʷ
wl0421 c4 = lw4 c4 (CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (K0⁻ ∷ []) tt tt Eq.refl

wl0422 : Complete 4 → ⟪ (S4 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ []) ⟫ʷ
wl0422 c4 = lw0 c4 (S4 ∷ []) (X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ []) tt tt Eq.refl

wl0423 : Complete 4 → ⟪ (S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (ι⁻ ∷ []) ⟫ʷ
wl0423 c4 = lw4 c4 (S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ []) (ι⁻ ∷ []) tt tt Eq.refl

wl0424 : Complete 4 → ⟪ (CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ []) ⟫ʷ
wl0424 c4 = lw4 c4 (CK10⁻ ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ []) tt tt Eq.refl

wl0425 : Complete 4 → ⟪ (CS01⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0425 c4 = lw4 c4 (CS01⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0426 : Complete 4 → ⟪ (CS01⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0426 c4 = lw4 c4 (CS01⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0427 : Complete 4 → ⟪ (CS01⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03 ∷ X1 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0427 c4 = lw4 c4 (CS01⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0428 : Complete 4 → ⟪ (CS01⁻ ∷ X1 ∷ CX43 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0428 c4 = lw2 c4 (CS01⁻ ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0429 : Complete 4 → ⟪ (CS01⁻ ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS23⁻ ∷ X1 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0429 c4 = lw4 c4 (CS01⁻ ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0430 : Complete 4 → ⟪ (CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS23 ∷ X1 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0430 c4 = lw4 c4 (CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0431 : Complete 4 → ⟪ (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wl0431 c4 = lw4 c4 (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl

wl0432 : Complete 4 → ⟪ (Toff201 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ Toff201 ∷ []) ⟫ʷ
wl0432 c4 = lw4 c4 (Toff201 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ Toff201 ∷ []) tt tt Eq.refl

wl0433 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) ⟫ʷ
wl0433 c4 = lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl

wl0434 : Complete 4 → ⟪ (CS23 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS23 ∷ []) ⟫ʷ
wl0434 c4 = lw4 c4 (CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ []) tt tt Eq.refl

wl0435 : Complete 4 → ⟪ (CX13 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CZ13 ∷ K3⁻ ∷ []) ⟫ʷ
wl0435 c4 = lw4 c4 (CX13 ∷ []) (K3 ∷ CZ13 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0436 : Complete 4 → ⟪ (CZ13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS02 ∷ X1 ∷ CZ13 ∷ []) ⟫ʷ
wl0436 c4 = lw4 c4 (CZ13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CZ13 ∷ []) tt tt Eq.refl

wl0437 : Complete 4 → ⟪ (CZ13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS24⁻ ∷ X1 ∷ CZ13 ∷ []) ⟫ʷ
wl0437 c4 = lw0 c4 (CZ13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CZ13 ∷ []) tt tt Eq.refl

wl0438 : Complete 4 → ⟪ (CZ13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS24 ∷ X1 ∷ CZ13 ∷ []) ⟫ʷ
wl0438 c4 = lw0 c4 (CZ13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CZ13 ∷ []) tt tt Eq.refl

wl0439 : Complete 4 → ⟪ (K3 ∷ CZ13 ∷ K3⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff213 ∷ X1 ∷ K3 ∷ CZ13 ∷ K3⁻ ∷ []) ⟫ʷ
wl0439 c4 = lw4 c4 (K3 ∷ CZ13 ∷ K3⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ K3 ∷ CZ13 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0440 : Complete 4 → ⟪ (CS23⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS23⁻ ∷ []) ⟫ʷ
wl0440 c4 = lw4 c4 (CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ []) tt tt Eq.refl

wl0441 : Complete 4 → ⟪ (CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) ⟫ʷ
wl0441 c4 = lw0 c4 (CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) tt tt Eq.refl

wl0442 : Complete 4 → ⟪ (CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) ⟫ʷ
wl0442 c4 = lw4 c4 (CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) tt tt Eq.refl

wl0443 : Complete 4 → ⟪ (CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
wl0443 c4 = lw0 c4 (CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0444 : Complete 4 → ⟪ (CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
wl0444 c4 = lw4 c4 (CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0445 : Complete 4 → ⟪ (CCZ123 ∷ X1 ∷ CS03 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
wl0445 c4 = lw4 c4 (CCZ123 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0446 : Complete 4 → ⟪ (CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ []) ⟫ʷ
wl0446 c4 = lw4 c4 (CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ []) tt tt Eq.refl

wl0447 : Complete 4 → ⟪ (CS14 ∷ X1 ∷ CS14 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ []) ⟫ʷ
wl0447 c4 = lw0 c4 (CS14 ∷ X1 ∷ CS14 ∷ X1 ∷ []) (X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ []) tt tt Eq.refl

wl0448 : Complete 4 → ⟪ (CS14 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ123 ∷ X1 ∷ CS14 ∷ []) ⟫ʷ
wl0448 c4 = lw0 c4 (CS14 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS14 ∷ []) tt tt Eq.refl

wl0449 : Complete 4 → ⟪ (CS14 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff314 ∷ X1 ∷ CS14 ∷ []) ⟫ʷ
wl0449 c4 = lw0 c4 (CS14 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS14 ∷ []) tt tt Eq.refl

wl0450 : Complete 4 → ⟪ (S1⁻ ∷ X1 ∷ CS14 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14 ∷ X1 ∷ S1⁻ ∷ []) ⟫ʷ
wl0450 c4 = lw0 c4 (S1⁻ ∷ X1 ∷ CS14 ∷ X1 ∷ []) (X1 ∷ CS14 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl

wl0451 : Complete 4 → ⟪ (S1⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S1⁻ ∷ []) ⟫ʷ
wl0451 c4 = lw4 c4 (S1⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl

wl0452 : Complete 4 → ⟪ (S1 ∷ X1 ∷ S1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S1 ∷ X1 ∷ S1 ∷ []) ⟫ʷ
wl0452 c4 = lw4 c4 (S1 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ S1 ∷ []) tt tt Eq.refl

wl0453 : Complete 4 → ⟪ (CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S1 ∷ X1 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0453 c4 = lw0 c4 (CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0454 : Complete 4 → ⟪ (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) ⟫ʷ
wl0454 c4 = lw0 c4 (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl

wl0455 : Complete 4 → ⟪ (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) ⟫ʷ
wl0455 c4 = lw4 c4 (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl

wl0456 : Complete 4 → ⟪ (Toff314 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ []) ⟫ʷ
wl0456 c4 = lw0 c4 (Toff314 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0457 : Complete 4 → ⟪ (Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ []) ⟫ʷ
wl0457 c4 = lw0 c4 (Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0458 : Complete 4 → ⟪ (CS03 ∷ X1 ∷ S1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S1 ∷ X1 ∷ CS03 ∷ []) ⟫ʷ
wl0458 c4 = lw4 c4 (CS03 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS03 ∷ []) tt tt Eq.refl

wl0459 : Complete 4 → ⟪ (CS03⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S1 ∷ X1 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0459 c4 = lw4 c4 (CS03⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0460 : Complete 4 → ⟪ (CK10 ∷ X1 ∷ S1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S1 ∷ X1 ∷ CK10 ∷ []) ⟫ʷ
wl0460 c4 = lw4 c4 (CK10 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CK10 ∷ []) tt tt Eq.refl

wl0461 : Complete 4 → ⟪ (CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) ⟫ʷ
wl0461 c4 = lw4 c4 (CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) tt tt Eq.refl

wl0462 : Complete 4 → ⟪ (CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) ⟫ʷ
wl0462 c4 = lw0 c4 (CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) tt tt Eq.refl

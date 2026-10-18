------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.Wins.WP02 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp0260 : Complete 4 → ⟪ (K0⁻ ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40⁻ ∷ X4 ∷ []) ⟫ʷ
wp0260 c4 = pw1 c4 (K0⁻ ∷ CK40 ∷ []) (X4 ∷ CK40⁻ ∷ X4 ∷ []) tt tt Eq.refl

wp0261 : Complete 4 → ⟪ (CCZ134 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ134 ∷ []) ⟫ʷ
wp0261 c4 = pw2 c4 (CCZ134 ∷ CS01 ∷ []) (CS01 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0262 : Complete 4 → ⟪ (CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wp0262 c4 = pw2 c4 (CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wp0263 : Complete 4 → ⟪ (CX24 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX24 ∷ []) ⟫ʷ
wp0263 c4 = pw1 c4 (CX24 ∷ Toff023 ∷ []) (Toff023 ∷ CX24 ∷ []) tt tt Eq.refl

wp0264 : Complete 4 → ⟪ (CCZ014 ∷ CX24 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ CCZ014 ∷ []) ⟫ʷ
wp0264 c4 = pw3 c4 (CCZ014 ∷ CX24 ∷ CCZ012 ∷ []) (CX24 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0265 : Complete 4 → ⟪ (CCZ014 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0265 c4 = pw3 c4 (CCZ014 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0266 : Complete 4 → ⟪ (CX24 ∷ CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ []) ⟫ʷ
wp0266 c4 = pw3 c4 (CX24 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX24 ∷ []) tt tt Eq.refl

wp0267 : Complete 4 → ⟪ (CX42 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX42 ∷ Toff034 ∷ []) ⟫ʷ
wp0267 c4 = pw1 c4 (CX42 ∷ Toff023 ∷ []) (Toff023 ∷ CX42 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0268 : Complete 4 → ⟪ (CCZ014 ∷ Toff034 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ014 ∷ []) ⟫ʷ
wp0268 c4 = pw2 c4 (CCZ014 ∷ Toff034 ∷ CCZ134 ∷ []) (Toff034 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0269 : Complete 4 → ⟪ (CCZ014 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CCZ014 ∷ []) ⟫ʷ
wp0269 c4 = pw3 c4 (CCZ014 ∷ CX42 ∷ []) (CX42 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0270 : Complete 4 → ⟪ (CX34 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX34 ∷ []) ⟫ʷ
wp0270 c4 = pw1 c4 (CX34 ∷ Toff023 ∷ []) (Toff023 ∷ CX34 ∷ []) tt tt Eq.refl

wp0271 : Complete 4 → ⟪ (CX42 ∷ Toff034 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ []) ⟫ʷ
wp0271 c4 = pw1 c4 (CX42 ∷ Toff034 ∷ Toff034 ∷ []) (CX42 ∷ []) tt tt Eq.refl

wp0272 : Complete 4 → ⟪ (CCZ014 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ014 ∷ []) ⟫ʷ
wp0272 c4 = pw2 c4 (CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0273 : Complete 4 → ⟪ (Sw24 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw24 ∷ []) ⟫ʷ
wp0273 c4 = pw1 c4 (Sw24 ∷ Toff023 ∷ []) (Toff034 ∷ Sw24 ∷ []) tt tt Eq.refl

wp0274 : Complete 4 → ⟪ (Sw24 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Sw24 ∷ []) ⟫ʷ
wp0274 c4 = pw1 c4 (Sw24 ∷ Toff304 ∷ []) (Toff302 ∷ Sw24 ∷ []) tt tt Eq.refl

wp0275 : Complete 4 → ⟪ (CCZ014 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ014 ∷ CCZ034 ∷ []) ⟫ʷ
wp0275 c4 = pw2 c4 (CCZ014 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0276 : Complete 4 → ⟪ (CCZ014 ∷ CCZ034 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ014 ∷ []) ⟫ʷ
wp0276 c4 = pw2 c4 (CCZ014 ∷ CCZ034 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0277 : Complete 4 → ⟪ (CS03 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS03 ∷ []) ⟫ʷ
wp0277 c4 = pw2 c4 (CS03 ∷ Toff134 ∷ []) (Toff134 ∷ CS03 ∷ []) tt tt Eq.refl

wp0278 : Complete 4 → ⟪ (CCZ234 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ234 ∷ []) ⟫ʷ
wp0278 c4 = pw1 c4 (CCZ234 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0279 : Complete 4 → ⟪ (CCZ234 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ234 ∷ []) ⟫ʷ
wp0279 c4 = pw1 c4 (CCZ234 ∷ CS02 ∷ []) (CS02 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0280 : Complete 4 → ⟪ (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
wp0280 c4 = pw1 c4 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl

wp0281 : Complete 4 → ⟪ (CX14 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX14 ∷ []) ⟫ʷ
wp0281 c4 = pw2 c4 (CX14 ∷ Toff013 ∷ []) (Toff013 ∷ CX14 ∷ []) tt tt Eq.refl

wp0282 : Complete 4 → ⟪ (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ024 ∷ []) ⟫ʷ
wp0282 c4 = pw3 c4 (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (CX14 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0283 : Complete 4 → ⟪ (CX14 ∷ CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wp0283 c4 = pw3 c4 (CX14 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wp0284 : Complete 4 → ⟪ (CX41 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX41 ∷ Toff034 ∷ []) ⟫ʷ
wp0284 c4 = pw2 c4 (CX41 ∷ Toff013 ∷ []) (Toff013 ∷ CX41 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0285 : Complete 4 → ⟪ (CCZ024 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ024 ∷ []) ⟫ʷ
wp0285 c4 = pw3 c4 (CCZ024 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0286 : Complete 4 → ⟪ (CX34 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX34 ∷ []) ⟫ʷ
wp0286 c4 = pw2 c4 (CX34 ∷ Toff013 ∷ []) (Toff013 ∷ CX34 ∷ []) tt tt Eq.refl

wp0287 : Complete 4 → ⟪ (CX41 ∷ Toff034 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wp0287 c4 = pw2 c4 (CX41 ∷ Toff034 ∷ Toff034 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wp0288 : Complete 4 → ⟪ (Sw14 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw14 ∷ []) ⟫ʷ
wp0288 c4 = pw2 c4 (Sw14 ∷ Toff013 ∷ []) (Toff034 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0289 : Complete 4 → ⟪ (Sw14 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Sw14 ∷ []) ⟫ʷ
wp0289 c4 = pw2 c4 (Sw14 ∷ Toff304 ∷ []) (Toff301 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0290 : Complete 4 → ⟪ (CCZ024 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ []) ⟫ʷ
wp0290 c4 = pw1 c4 (CCZ024 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0291 : Complete 4 → ⟪ (CCZ024 ∷ CCZ034 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ024 ∷ []) ⟫ʷ
wp0291 c4 = pw1 c4 (CCZ024 ∷ CCZ034 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0292 : Complete 4 → ⟪ (CS03 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CS03 ∷ []) ⟫ʷ
wp0292 c4 = pw1 c4 (CS03 ∷ Toff234 ∷ []) (Toff234 ∷ CS03 ∷ []) tt tt Eq.refl

wp0293 : Complete 4 → ⟪ (CCZ134 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ134 ∷ []) ⟫ʷ
wp0293 c4 = pw2 c4 (CCZ134 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0294 : Complete 4 → ⟪ (CCZ234 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ234 ∷ []) ⟫ʷ
wp0294 c4 = pw1 c4 (CCZ234 ∷ CS03 ∷ []) (CS03 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0295 : Complete 4 → ⟪ (CCZ034 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) ⟫ʷ
wp0295 c4 = pw1 c4 (CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0296 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) ⟫ʷ
wp0296 c4 = pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) tt tt Eq.refl

wp0297 : Complete 4 → ⟪ (CCZ024 ∷ CCZ034 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ034 ∷ []) ⟫ʷ
wp0297 c4 = pw1 c4 (CCZ024 ∷ CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0298 : Complete 4 → ⟪ (CS02 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS02 ∷ []) ⟫ʷ
wp0298 c4 = pw1 c4 (CS02 ∷ Toff324 ∷ []) (Toff324 ∷ CS02 ∷ []) tt tt Eq.refl

wp0299 : Complete 4 → ⟪ (CCZ013 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ013 ∷ []) ⟫ʷ
wp0299 c4 = pw2 c4 (CCZ013 ∷ CS14 ∷ []) (CS14 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0300 : Complete 4 → ⟪ (CCZ124 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ124 ∷ []) ⟫ʷ
wp0300 c4 = pw3 c4 (CCZ124 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0301 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) ⟫ʷ
wp0301 c4 = pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) tt tt Eq.refl

wp0302 : Complete 4 → ⟪ (CCZ234 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ234 ∷ []) ⟫ʷ
wp0302 c4 = pw1 c4 (CCZ234 ∷ CS04 ∷ []) (CS04 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0303 : Complete 4 → ⟪ (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ []) ⟫ʷ
wp0303 c4 = pw2 c4 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (Toff401 ∷ []) tt tt Eq.refl

wp0304 : Complete 4 → ⟪ (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ014 ∷ []) ⟫ʷ
wp0304 c4 = pw2 c4 (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) (Toff401 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0305 : Complete 4 → ⟪ (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
wp0305 c4 = pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl

wp0306 : Complete 4 → ⟪ (Toff401 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0306 c4 = pw2 c4 (Toff401 ∷ Toff401 ∷ []) [] tt tt Eq.refl

wp0307 : Complete 4 → ⟪ (CCZ034 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ023 ∷ CCZ034 ∷ []) ⟫ʷ
wp0307 c4 = pw1 c4 (CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0308 : Complete 4 → ⟪ (CCZ014 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ CCZ014 ∷ []) ⟫ʷ
wp0308 c4 = pw3 c4 (CCZ014 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0309 : Complete 4 → ⟪ (CCZ023 ∷ CCZ034 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ034 ∷ []) ⟫ʷ
wp0309 c4 = pw1 c4 (CCZ023 ∷ CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0310 : Complete 4 → ⟪ (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ014 ∷ []) ⟫ʷ
wp0310 c4 = pw3 c4 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (Toff012 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0311 : Complete 4 → ⟪ (CS02 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS02 ∷ []) ⟫ʷ
wp0311 c4 = pw1 c4 (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) tt tt Eq.refl

wp0312 : Complete 4 → ⟪ (CCZ034 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ034 ∷ []) ⟫ʷ
wp0312 c4 = pw2 c4 (CCZ034 ∷ CS13 ∷ []) (CS13 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0313 : Complete 4 → ⟪ (CCZ034 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0313 c4 = pw1 c4 (CCZ034 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0314 : Complete 4 → ⟪ (CCZ034 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ034 ∷ []) ⟫ʷ
wp0314 c4 = pw1 c4 (CCZ034 ∷ CS23 ∷ []) (CS23 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0315 : Complete 4 → ⟪ (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ []) ⟫ʷ
wp0315 c4 = pw1 c4 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (Toff403 ∷ []) tt tt Eq.refl

wp0316 : Complete 4 → ⟪ (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
wp0316 c4 = pw1 c4 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (Toff403 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0317 : Complete 4 → ⟪ (Toff403 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0317 c4 = pw1 c4 (Toff403 ∷ Toff403 ∷ []) [] tt tt Eq.refl

wp0318 : Complete 4 → ⟪ (CCZ124 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ CCZ124 ∷ []) ⟫ʷ
wp0318 c4 = pw3 c4 (CCZ124 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0319 : Complete 4 → ⟪ (CS04⁻ ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0319 c4 = pw1 c4 (CS04⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0320 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) ⟫ʷ
wp0320 c4 = pw1 c4 (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) tt tt Eq.refl

wp0321 : Complete 4 → ⟪ (CCZ124 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ CCZ124 ∷ []) ⟫ʷ
wp0321 c4 = pw3 c4 (CCZ124 ∷ CX40 ∷ []) (CX40 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0322 : Complete 4 → ⟪ (CCZ034 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CZ03 ∷ CCZ034 ∷ []) ⟫ʷ
wp0322 c4 = pw1 c4 (CCZ034 ∷ Toff403 ∷ []) (Toff403 ∷ CZ03 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0323 : Complete 4 → ⟪ (CS03⁻ ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0323 c4 = pw1 c4 (CS03⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0324 : Complete 4 → ⟪ (CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ CS03⁻ ∷ CZ03 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ []) ⟫ʷ
wp0324 c4 = pw1 c4 (CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ CS03⁻ ∷ CZ03 ∷ CCZ034 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl

wp0325 : Complete 4 → ⟪ (CS04 ∷ CS03 ∷ CCZ034 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CS04 ∷ []) ⟫ʷ
wp0325 c4 = pw1 c4 (CS04 ∷ CS03 ∷ CCZ034 ∷ CX34 ∷ []) (CX34 ∷ CS04 ∷ []) tt tt Eq.refl

wp0326 : Complete 4 → ⟪ (CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0326 c4 = pw1 c4 (CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ CX34 ∷ []) (CX34 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0327 : Complete 4 → ⟪ (CCZ034 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ034 ∷ []) ⟫ʷ
wp0327 c4 = pw1 c4 (CCZ034 ∷ CS03 ∷ []) (CS03 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0328 : Complete 4 → ⟪ (CS03 ∷ CS04⁻ ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ []) ⟫ʷ
wp0328 c4 = pw1 c4 (CS03 ∷ CS04⁻ ∷ CS03⁻ ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl

wp0329 : Complete 4 → ⟪ (CCZ034 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0329 c4 = pw1 c4 (CCZ034 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0330 : Complete 4 → ⟪ (CX20 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CX20 ∷ []) ⟫ʷ
wp0330 c4 = pw3 c4 (CX20 ∷ Toff412 ∷ []) (Toff412 ∷ CX20 ∷ []) tt tt Eq.refl

wp0331 : Complete 4 → ⟪ (CX02 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CX02 ∷ Toff401 ∷ []) ⟫ʷ
wp0331 c4 = pw3 c4 (CX02 ∷ Toff412 ∷ []) (Toff412 ∷ CX02 ∷ Toff401 ∷ []) tt tt Eq.refl

wp0332 : Complete 4 → ⟪ (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ034 ∷ []) ⟫ʷ
wp0332 c4 = pw2 c4 (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (Toff401 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0333 : Complete 4 → ⟪ (CCZ034 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ CCZ034 ∷ []) ⟫ʷ
wp0333 c4 = pw1 c4 (CCZ034 ∷ CX02 ∷ []) (CX02 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0334 : Complete 4 → ⟪ (CX10 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CX10 ∷ []) ⟫ʷ
wp0334 c4 = pw3 c4 (CX10 ∷ Toff412 ∷ []) (Toff412 ∷ CX10 ∷ []) tt tt Eq.refl

wp0335 : Complete 4 → ⟪ (Toff401 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff401 ∷ []) ⟫ʷ
wp0335 c4 = pw3 c4 (Toff401 ∷ Toff412 ∷ []) (Toff412 ∷ Toff401 ∷ []) tt tt Eq.refl

wp0336 : Complete 4 → ⟪ (CX02 ∷ Toff401 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
wp0336 c4 = pw3 c4 (CX02 ∷ Toff401 ∷ Toff401 ∷ []) (CX02 ∷ []) tt tt Eq.refl

wp0337 : Complete 4 → ⟪ (CCZ014 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Sw02 ∷ CCZ124 ∷ []) ⟫ʷ
wp0337 c4 = pw3 c4 (CCZ014 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0338 : Complete 4 → ⟪ (Sw02 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw02 ∷ []) ⟫ʷ
wp0338 c4 = pw3 c4 (Sw02 ∷ Toff412 ∷ []) (Toff401 ∷ Sw02 ∷ []) tt tt Eq.refl

wp0339 : Complete 4 → ⟪ (CCZ124 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Sw02 ∷ CCZ014 ∷ []) ⟫ʷ
wp0339 c4 = pw3 c4 (CCZ124 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0340 : Complete 4 → ⟪ (Sw02 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Sw02 ∷ []) ⟫ʷ
wp0340 c4 = pw3 c4 (Sw02 ∷ Toff104 ∷ []) (Toff124 ∷ Sw02 ∷ []) tt tt Eq.refl

wp0341 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) ⟫ʷ
wp0341 c4 = pw2 c4 (CCZ014 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) tt tt Eq.refl

wp0342 : Complete 4 → ⟪ (CCZ234 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ CCZ234 ∷ []) ⟫ʷ
wp0342 c4 = pw1 c4 (CCZ234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0343 : Complete 4 → ⟪ (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ []) ⟫ʷ
wp0343 c4 = pw1 c4 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl

wp0344 : Complete 4 → ⟪ (CCZ034 ∷ CZ04 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
wp0344 c4 = pw1 c4 (CCZ034 ∷ CZ04 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0345 : Complete 4 → ⟪ (CCZ034 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ Toff304 ∷ []) ⟫ʷ
wp0345 c4 = pw1 c4 (CCZ034 ∷ CZ04 ∷ []) (Toff304 ∷ CCZ034 ∷ Toff304 ∷ []) tt tt Eq.refl

wp0346 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ CCZ034 ∷ CZ04 ∷ []) ⟫ʷ
wp0346 c4 = pw1 c4 (CCZ034 ∷ []) (CZ04 ∷ CCZ034 ∷ CZ04 ∷ []) tt tt Eq.refl

wp0347 : Complete 4 → ⟪ (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
wp0347 c4 = pw1 c4 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0348 : Complete 4 → ⟪ (CS04⁻ ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS04⁻ ∷ []) ⟫ʷ
wp0348 c4 = pw1 c4 (CS04⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0349 : Complete 4 → ⟪ (CS04⁻ ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0349 c4 = pw1 c4 (CS04⁻ ∷ S3 ∷ []) (S3 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0350 : Complete 4 → ⟪ (CS04⁻ ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS04⁻ ∷ []) ⟫ʷ
wp0350 c4 = pw3 c4 (CS04⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0351 : Complete 4 → ⟪ (Toff304 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0351 c4 = pw1 c4 (Toff304 ∷ Toff304 ∷ []) [] tt tt Eq.refl

wp0352 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) ⟫ʷ
wp0352 c4 = pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) tt tt Eq.refl

wp0353 : Complete 4 → ⟪ (CCZ034 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) ⟫ʷ
wp0353 c4 = pw1 c4 (CCZ034 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) tt tt Eq.refl

wp0354 : Complete 4 → ⟪ (CCZ034 ∷ CZ04 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ []) ⟫ʷ
wp0354 c4 = pw1 c4 (CCZ034 ∷ CZ04 ∷ Toff304 ∷ CCZ034 ∷ []) (Toff304 ∷ []) tt tt Eq.refl

wp0355 : Complete 4 → ⟪ (CCZ014 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ014 ∷ CZ01 ∷ []) ⟫ʷ
wp0355 c4 = pw2 c4 (CCZ014 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl

wp0356 : Complete 4 → ⟪ (CCZ014 ∷ CZ01 ∷ Toff401 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ []) ⟫ʷ
wp0356 c4 = pw2 c4 (CCZ014 ∷ CZ01 ∷ Toff401 ∷ CCZ014 ∷ []) (Toff401 ∷ []) tt tt Eq.refl

wp0357 : Complete 4 → ⟪ (CCZ034 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ034 ∷ []) ⟫ʷ
wp0357 c4 = pw2 c4 (CCZ034 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0358 : Complete 4 → ⟪ (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ []) ⟫ʷ
wp0358 c4 = pw2 c4 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (Toff401 ∷ []) tt tt Eq.refl

wp0359 : Complete 4 → ⟪ (CCZ012 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ012 ∷ []) ⟫ʷ
wp0359 c4 = pw3 c4 (CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0360 : Complete 4 → ⟪ (CX02 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CX02 ∷ []) ⟫ʷ
wp0360 c4 = pw3 c4 (CX02 ∷ Toff401 ∷ []) (Toff401 ∷ CX02 ∷ []) tt tt Eq.refl

wp0361 : Complete 4 → ⟪ (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ CCZ234 ∷ []) ⟫ʷ
wp0361 c4 = pw1 c4 (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) (CX02 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0362 : Complete 4 → ⟪ (CCZ034 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ034 ∷ CCZ013 ∷ []) ⟫ʷ
wp0362 c4 = pw2 c4 (CCZ034 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0363 : Complete 4 → ⟪ (CCZ234 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ234 ∷ []) ⟫ʷ
wp0363 c4 = pw1 c4 (CCZ234 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0364 : Complete 4 → ⟪ (CX02 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
wp0364 c4 = pw1 c4 (CX02 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX02 ∷ []) tt tt Eq.refl

wp0365 : Complete 4 → ⟪ (CX20 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CX20 ∷ Toff412 ∷ []) ⟫ʷ
wp0365 c4 = pw3 c4 (CX20 ∷ Toff401 ∷ []) (Toff401 ∷ CX20 ∷ Toff412 ∷ []) tt tt Eq.refl

wp0366 : Complete 4 → ⟪ (CCZ234 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ234 ∷ []) ⟫ʷ
wp0366 c4 = pw1 c4 (CCZ234 ∷ CX20 ∷ []) (CX20 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0367 : Complete 4 → ⟪ (CS13 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS13 ∷ []) ⟫ʷ
wp0367 c4 = pw2 c4 (CS13 ∷ Toff401 ∷ []) (Toff401 ∷ CS13 ∷ []) tt tt Eq.refl

wp0368 : Complete 4 → ⟪ (CX12 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CX12 ∷ []) ⟫ʷ
wp0368 c4 = pw3 c4 (CX12 ∷ Toff401 ∷ []) (Toff401 ∷ CX12 ∷ []) tt tt Eq.refl

wp0369 : Complete 4 → ⟪ (CX20 ∷ Toff412 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
wp0369 c4 = pw3 c4 (CX20 ∷ Toff412 ∷ Toff412 ∷ []) (CX20 ∷ []) tt tt Eq.refl

wp0370 : Complete 4 → ⟪ (Sw02 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw02 ∷ []) ⟫ʷ
wp0370 c4 = pw3 c4 (Sw02 ∷ Toff401 ∷ []) (Toff412 ∷ Sw02 ∷ []) tt tt Eq.refl

wp0371 : Complete 4 → ⟪ (Sw02 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw02 ∷ []) ⟫ʷ
wp0371 c4 = pw3 c4 (Sw02 ∷ Toff124 ∷ []) (Toff104 ∷ Sw02 ∷ []) tt tt Eq.refl

wp0372 : Complete 4 → ⟪ (CCZ034 ∷ CZ03 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ034 ∷ []) ⟫ʷ
wp0372 c4 = pw1 c4 (CCZ034 ∷ CZ03 ∷ CX34 ∷ []) (CX34 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0373 : Complete 4 → ⟪ (CCZ034 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ034 ∷ CX34 ∷ []) ⟫ʷ
wp0373 c4 = pw1 c4 (CCZ034 ∷ CZ03 ∷ []) (CX34 ∷ CCZ034 ∷ CX34 ∷ []) tt tt Eq.refl

wp0374 : Complete 4 → ⟪ (CCZ012 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ012 ∷ []) ⟫ʷ
wp0374 c4 = pw3 c4 (CCZ012 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0375 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CCZ034 ∷ CZ03 ∷ []) ⟫ʷ
wp0375 c4 = pw1 c4 (CCZ034 ∷ []) (CZ03 ∷ CCZ034 ∷ CZ03 ∷ []) tt tt Eq.refl

wp0376 : Complete 4 → ⟪ (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ014 ∷ []) ⟫ʷ
wp0376 c4 = pw3 c4 (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) (Toff412 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0377 : Complete 4 → ⟪ (CCZ034 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ []) ⟫ʷ
wp0377 c4 = pw2 c4 (CCZ034 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0378 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ CCZ014 ∷ CX02 ∷ []) ⟫ʷ
wp0378 c4 = pw3 c4 (CCZ014 ∷ []) (CX02 ∷ CCZ014 ∷ CX02 ∷ []) tt tt Eq.refl

wp0379 : Complete 4 → ⟪ (CS14 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS14 ∷ []) ⟫ʷ
wp0379 c4 = pw2 c4 (CS14 ∷ Toff301 ∷ []) (Toff301 ∷ CS14 ∷ []) tt tt Eq.refl

wp0380 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ124 ∷ CX20 ∷ []) ⟫ʷ
wp0380 c4 = pw3 c4 (CCZ124 ∷ []) (CX20 ∷ CCZ124 ∷ CX20 ∷ []) tt tt Eq.refl

wp0381 : Complete 4 → ⟪ (CCZ014 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) ⟫ʷ
wp0381 c4 = pw3 c4 (CCZ014 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0382 : Complete 4 → ⟪ (CCZ124 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) ⟫ʷ
wp0382 c4 = pw3 c4 (CCZ124 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0383 : Complete 4 → ⟪ (CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp0383 c4 = pw3 c4 (CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp0384 : Complete 4 → ⟪ (CCZ124 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ124 ∷ []) ⟫ʷ
wp0384 c4 = pw3 c4 (CCZ124 ∷ CS04 ∷ []) (CS04 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0385 : Complete 4 → ⟪ (CS04 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS04 ∷ CS03 ∷ CCZ034 ∷ []) ⟫ʷ
wp0385 c4 = pw1 c4 (CS04 ∷ Toff403 ∷ []) (Toff403 ∷ CS04 ∷ CS03 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0386 : Complete 4 → ⟪ (CS03 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS03 ∷ []) ⟫ʷ
wp0386 c4 = pw1 c4 (CS03 ∷ Toff403 ∷ []) (Toff403 ∷ CS03 ∷ []) tt tt Eq.refl

wp0387 : Complete 4 → ⟪ (CS04 ∷ CS03 ∷ CCZ034 ∷ CS03 ∷ CZ03 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
wp0387 c4 = pw1 c4 (CS04 ∷ CS03 ∷ CCZ034 ∷ CS03 ∷ CZ03 ∷ CCZ034 ∷ []) (CS04 ∷ []) tt tt Eq.refl

wp0388 : Complete 4 → ⟪ (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ034 ∷ []) ⟫ʷ
wp0388 c4 = pw2 c4 (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) (Toff301 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0389 : Complete 4 → ⟪ (CCZ124 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ124 ∷ []) ⟫ʷ
wp0389 c4 = pw3 c4 (CCZ124 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0390 : Complete 4 → ⟪ (CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wp0390 c4 = pw3 c4 (CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wp0391 : Complete 4 → ⟪ (CCZ014 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ012 ∷ CCZ014 ∷ []) ⟫ʷ
wp0391 c4 = pw3 c4 (CCZ014 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0392 : Complete 4 → ⟪ (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ013 ∷ []) ⟫ʷ
wp0392 c4 = pw2 c4 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (CX43 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0393 : Complete 4 → ⟪ (CS04 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS04 ∷ []) ⟫ʷ
wp0393 c4 = pw1 c4 (CS04 ∷ Toff324 ∷ []) (Toff324 ∷ CS04 ∷ []) tt tt Eq.refl

wp0394 : Complete 4 → ⟪ (CCZ013 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ013 ∷ []) ⟫ʷ
wp0394 c4 = pw2 c4 (CCZ013 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0395 : Complete 4 → ⟪ (CX43 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ []) ⟫ʷ
wp0395 c4 = pw2 c4 (CX43 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX43 ∷ []) tt tt Eq.refl

wp0396 : Complete 4 → ⟪ (CS04 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CS04 ∷ []) ⟫ʷ
wp0396 c4 = pw1 c4 (CS04 ∷ CX43 ∷ []) (CX43 ∷ CS04 ∷ []) tt tt Eq.refl

wp0397 : Complete 4 → ⟪ (CS04⁻ ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0397 c4 = pw1 c4 (CS04⁻ ∷ CX43 ∷ []) (CX43 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0398 : Complete 4 → ⟪ (CCZ014 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ013 ∷ []) ⟫ʷ
wp0398 c4 = pw2 c4 (CCZ014 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0399 : Complete 4 → ⟪ (Sw34 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw34 ∷ []) ⟫ʷ
wp0399 c4 = pw2 c4 (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0400 : Complete 4 → ⟪ (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) ⟫ʷ
wp0400 c4 = pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) tt tt Eq.refl

wp0401 : Complete 4 → ⟪ (CS03 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CS04 ∷ []) ⟫ʷ
wp0401 c4 = pw1 c4 (CS03 ∷ Sw34 ∷ []) (Sw34 ∷ CS04 ∷ []) tt tt Eq.refl

wp0402 : Complete 4 → ⟪ (CS03⁻ ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0402 c4 = pw1 c4 (CS03⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0403 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0403 c4 = pw1 c4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0404 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0404 c4 = pw1 c4 (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0405 : Complete 4 → ⟪ (CCZ024 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0405 c4 = pw1 c4 (CCZ024 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0406 : Complete 4 → ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0406 c4 = pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0407 : Complete 4 → ⟪ (CCZ014 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0407 c4 = pw2 c4 (CCZ014 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0408 : Complete 4 → ⟪ (Toff023 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ Toff023 ∷ []) ⟫ʷ
wp0408 c4 = pw1 c4 (Toff023 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0409 : Complete 4 → ⟪ (Toff013 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ Toff013 ∷ []) ⟫ʷ
wp0409 c4 = pw2 c4 (Toff013 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0410 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wp0410 c4 = pw1 c4 (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wp0411 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0411 c4 = pw1 c4 (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0412 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wp0412 c4 = pw2 c4 (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0413 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wp0413 c4 = pw1 c4 (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wp0414 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wp0414 c4 = pw1 c4 (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wp0415 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0415 c4 = pw1 c4 (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0416 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wp0416 c4 = pw2 c4 (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wp0417 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wp0417 c4 = pw1 c4 (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wp0418 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wp0418 c4 = pw1 c4 (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wp0419 : Complete 4 → ⟪ (CCZ024 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0419 c4 = pw1 c4 (CCZ024 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0420 : Complete 4 → ⟪ (CCZ024 ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS04⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0420 c4 = pw1 c4 (CCZ024 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0421 : Complete 4 → ⟪ (S0 ∷ CS04⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0421 c4 = pw2 c4 (S0 ∷ CS04⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0422 : Complete 4 → ⟪ (CS04⁻ ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0422 c4 = pw2 c4 (CS04⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0423 : Complete 4 → ⟪ (CS14⁻ ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0423 c4 = pw2 c4 (CS14⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0424 : Complete 4 → ⟪ (CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ CS14⁻ ∷ CZ14 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ []) ⟫ʷ
wp0424 c4 = pw2 c4 (CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ CS14⁻ ∷ CZ14 ∷ CCZ014 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl

wp0425 : Complete 4 → ⟪ (S0 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ S0 ∷ CS14 ∷ CCZ014 ∷ []) ⟫ʷ
wp0425 c4 = pw2 c4 (S0 ∷ Toff014 ∷ []) (Toff014 ∷ S0 ∷ CS14 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0426 : Complete 4 → ⟪ (CS14 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS14 ∷ []) ⟫ʷ
wp0426 c4 = pw2 c4 (CS14 ∷ Toff014 ∷ []) (Toff014 ∷ CS14 ∷ []) tt tt Eq.refl

wp0427 : Complete 4 → ⟪ (S0 ∷ CS14 ∷ CCZ014 ∷ CS14 ∷ CZ14 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
wp0427 c4 = pw2 c4 (S0 ∷ CS14 ∷ CCZ014 ∷ CS14 ∷ CZ14 ∷ CCZ014 ∷ []) (S0 ∷ []) tt tt Eq.refl

wp0428 : Complete 4 → ⟪ (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ []) ⟫ʷ
wp0428 c4 = pw1 c4 (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wp0429 : Complete 4 → ⟪ (CS13 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS13 ∷ []) ⟫ʷ
wp0429 c4 = pw2 c4 (CS13 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS13 ∷ []) tt tt Eq.refl

wp0430 : Complete 4 → ⟪ (CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS13⁻ ∷ []) ⟫ʷ
wp0430 c4 = pw2 c4 (CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0431 : Complete 4 → ⟪ (CS04⁻ ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0431 c4 = pw1 c4 (CS04⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0432 : Complete 4 → ⟪ (CS24⁻ ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS24⁻ ∷ []) ⟫ʷ
wp0432 c4 = pw1 c4 (CS24⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp0433 : Complete 4 → ⟪ (CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ CS24⁻ ∷ CZ24 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ []) ⟫ʷ
wp0433 c4 = pw1 c4 (CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ CS24⁻ ∷ CZ24 ∷ CCZ024 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl

wp0434 : Complete 4 → ⟪ (S0 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ S0 ∷ CS24 ∷ CCZ024 ∷ []) ⟫ʷ
wp0434 c4 = pw1 c4 (S0 ∷ Toff024 ∷ []) (Toff024 ∷ S0 ∷ CS24 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0435 : Complete 4 → ⟪ (CS24 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS24 ∷ []) ⟫ʷ
wp0435 c4 = pw1 c4 (CS24 ∷ Toff024 ∷ []) (Toff024 ∷ CS24 ∷ []) tt tt Eq.refl

wp0436 : Complete 4 → ⟪ (S0 ∷ CS24 ∷ CCZ024 ∷ CS24 ∷ CZ24 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
wp0436 c4 = pw1 c4 (S0 ∷ CS24 ∷ CCZ024 ∷ CS24 ∷ CZ24 ∷ CCZ024 ∷ []) (S0 ∷ []) tt tt Eq.refl

wp0437 : Complete 4 → ⟪ (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ []) ⟫ʷ
wp0437 c4 = pw2 c4 (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ []) tt tt Eq.refl

wp0438 : Complete 4 → ⟪ (CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ []) ⟫ʷ
wp0438 c4 = pw3 c4 (CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ []) tt tt Eq.refl

wp0439 : Complete 4 → ⟪ (CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0439 c4 = pw3 c4 (CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0440 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0440 c4 = pw2 c4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0441 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0441 c4 = pw2 c4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0442 : Complete 4 → ⟪ (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0442 c4 = pw3 c4 (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0443 : Complete 4 → ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0443 c4 = pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0444 : Complete 4 → ⟪ (CCZ014 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0444 c4 = pw2 c4 (CCZ014 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0445 : Complete 4 → ⟪ (CCZ014 ∷ S1 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS14⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0445 c4 = pw2 c4 (CCZ014 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0446 : Complete 4 → ⟪ (Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ Toff013 ∷ []) ⟫ʷ
wp0446 c4 = pw2 c4 (Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0447 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0447 c4 = pw1 c4 (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0448 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0448 c4 = pw1 c4 (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0449 : Complete 4 → ⟪ (CS24⁻ ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0449 c4 = pw1 c4 (CS24⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0450 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) ⟫ʷ
wp0450 c4 = pw3 c4 (CCZ024 ∷ []) (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) tt tt Eq.refl

wp0451 : Complete 4 → ⟪ (CS04⁻ ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0451 c4 = pw1 c4 (CS04⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0452 : Complete 4 → ⟪ (CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ CS04⁻ ∷ CZ04 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ []) ⟫ʷ
wp0452 c4 = pw1 c4 (CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ CS04⁻ ∷ CZ04 ∷ CCZ024 ∷ []) (CS24⁻ ∷ []) tt tt Eq.refl

wp0453 : Complete 4 → ⟪ (S2 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ S2 ∷ CS04 ∷ CCZ024 ∷ []) ⟫ʷ
wp0453 c4 = pw1 c4 (S2 ∷ Toff204 ∷ []) (Toff204 ∷ S2 ∷ CS04 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0454 : Complete 4 → ⟪ (CS04 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS04 ∷ []) ⟫ʷ
wp0454 c4 = pw1 c4 (CS04 ∷ Toff204 ∷ []) (Toff204 ∷ CS04 ∷ []) tt tt Eq.refl

wp0455 : Complete 4 → ⟪ (S2 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ []) ⟫ʷ
wp0455 c4 = pw1 c4 (S2 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) (S2 ∷ []) tt tt Eq.refl

wp0456 : Complete 4 → ⟪ (CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ []) ⟫ʷ
wp0456 c4 = pw1 c4 (CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0457 : Complete 4 → ⟪ (CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0457 c4 = pw1 c4 (CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0458 : Complete 4 → ⟪ (CCZ014 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0458 c4 = pw3 c4 (CCZ014 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0459 : Complete 4 → ⟪ (Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ Toff023 ∷ []) ⟫ʷ
wp0459 c4 = pw1 c4 (Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0460 : Complete 4 → ⟪ (CCZ024 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0460 c4 = pw1 c4 (CCZ024 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0461 : Complete 4 → ⟪ (CCZ024 ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS24⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0461 c4 = pw1 c4 (CCZ024 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0462 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0462 c4 = pw1 c4 (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0463 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0463 c4 = pw1 c4 (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0464 : Complete 4 → ⟪ (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0464 c4 = pw1 c4 (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0465 : Complete 4 → ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0465 c4 = pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0466 : Complete 4 → ⟪ (CCZ014 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0466 c4 = pw2 c4 (CCZ014 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0467 : Complete 4 → ⟪ (Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ Toff023 ∷ []) ⟫ʷ
wp0467 c4 = pw1 c4 (Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0468 : Complete 4 → ⟪ (Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ Toff013 ∷ []) ⟫ʷ
wp0468 c4 = pw2 c4 (Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0469 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wp0469 c4 = pw1 c4 (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wp0470 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0470 c4 = pw1 c4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0471 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wp0471 c4 = pw2 c4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0472 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wp0472 c4 = pw1 c4 (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wp0473 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wp0473 c4 = pw1 c4 (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

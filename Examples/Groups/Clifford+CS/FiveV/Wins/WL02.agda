------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.Wins.WL02 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl0247 : Complete 4 → ⟪ (CS12 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS12 ∷ []) ⟫ʷ
wl0247 c4 = lw4 c4 (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) tt tt Eq.refl

wl0248 : Complete 4 → ⟪ (CCZ234 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ CS23 ∷ []) ⟫ʷ
wl0248 c4 = lw0 c4 (CCZ234 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ []) (Toff134 ∷ CS12 ∷ CS23 ∷ []) tt tt Eq.refl

wl0249 : Complete 4 → ⟪ (CS23 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0249 c4 = lw0 c4 (CS23 ∷ []) (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0250 : Complete 4 → ⟪ (CX32 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CX32 ∷ Toff013 ∷ []) ⟫ʷ
wl0250 c4 = lw4 c4 (CX32 ∷ Toff012 ∷ []) (Toff012 ∷ CX32 ∷ Toff013 ∷ []) tt tt Eq.refl

wl0251 : Complete 4 → ⟪ (CX13 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CX13 ∷ []) ⟫ʷ
wl0251 c4 = lw4 c4 (CX13 ∷ Toff012 ∷ []) (Toff012 ∷ CX13 ∷ []) tt tt Eq.refl

wl0252 : Complete 4 → ⟪ (Toff012 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff012 ∷ []) ⟫ʷ
wl0252 c4 = lw4 c4 (Toff012 ∷ Toff013 ∷ []) (Toff013 ∷ Toff012 ∷ []) tt tt Eq.refl

wl0253 : Complete 4 → ⟪ (CX32 ∷ Toff013 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
wl0253 c4 = lw4 c4 (CX32 ∷ Toff013 ∷ Toff013 ∷ []) (CX32 ∷ []) tt tt Eq.refl

wl0254 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ134 ∷ CX32 ∷ []) ⟫ʷ
wl0254 c4 = lw0 c4 (CCZ134 ∷ []) (CX32 ∷ CCZ134 ∷ CX32 ∷ []) tt tt Eq.refl

wl0255 : Complete 4 → ⟪ (CX23 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CX23 ∷ []) ⟫ʷ
wl0255 c4 = lw4 c4 (CX23 ∷ Toff012 ∷ []) (Toff012 ∷ CX23 ∷ []) tt tt Eq.refl

wl0256 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) ⟫ʷ
wl0256 c4 = lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl

wl0257 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ124 ∷ CX23 ∷ []) ⟫ʷ
wl0257 c4 = lw0 c4 (CCZ124 ∷ []) (CX23 ∷ CCZ124 ∷ CX23 ∷ []) tt tt Eq.refl

wl0258 : Complete 4 → ⟪ (CX23 ∷ CX32 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ []) ⟫ʷ
wl0258 c4 = lw4 c4 (CX23 ∷ CX32 ∷ CX23 ∷ []) (Sw23 ∷ []) tt tt Eq.refl

wl0259 : Complete 4 → ⟪ (CCZ124 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) ⟫ʷ
wl0259 c4 = lw0 c4 (CCZ124 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0260 : Complete 4 → ⟪ (CCZ124 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ124 ∷ []) ⟫ʷ
wl0260 c4 = lw0 c4 (CCZ124 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0261 : Complete 4 → ⟪ (CCZ134 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) ⟫ʷ
wl0261 c4 = lw0 c4 (CCZ134 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0262 : Complete 4 → ⟪ (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wl0262 c4 = lw0 c4 (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wl0263 : Complete 4 → ⟪ (CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0263 c4 = lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl

wl0264 : Complete 4 → ⟪ (CCZ013 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ012 ∷ []) ⟫ʷ
wl0264 c4 = lw4 c4 (CCZ013 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0265 : Complete 4 → ⟪ (Sw23 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sw23 ∷ []) ⟫ʷ
wl0265 c4 = lw4 c4 (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0266 : Complete 4 → ⟪ (CCZ012 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ013 ∷ []) ⟫ʷ
wl0266 c4 = lw4 c4 (CCZ012 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0267 : Complete 4 → ⟪ (Sw23 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ Sw23 ∷ []) ⟫ʷ
wl0267 c4 = lw4 c4 (Sw23 ∷ Toff103 ∷ []) (Toff102 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0268 : Complete 4 → ⟪ (CCZ012 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ012 ∷ []) ⟫ʷ
wl0268 c4 = lw4 c4 (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0269 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) ⟫ʷ
wl0269 c4 = lw4 c4 (CCZ012 ∷ []) (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) tt tt Eq.refl

wl0270 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) ⟫ʷ
wl0270 c4 = lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl

wl0271 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) ⟫ʷ
wl0271 c4 = lw0 c4 (CCZ124 ∷ []) (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) tt tt Eq.refl

wl0272 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ124 ∷ CX13 ∷ []) ⟫ʷ
wl0272 c4 = lw0 c4 (CCZ124 ∷ []) (CX13 ∷ CCZ124 ∷ CX13 ∷ []) tt tt Eq.refl

wl0273 : Complete 4 → ⟪ (CX31 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CX31 ∷ Toff023 ∷ []) ⟫ʷ
wl0273 c4 = lw4 c4 (CX31 ∷ Toff012 ∷ []) (Toff012 ∷ CX31 ∷ Toff023 ∷ []) tt tt Eq.refl

wl0274 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) ⟫ʷ
wl0274 c4 = lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl

wl0275 : Complete 4 → ⟪ (Toff012 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff012 ∷ []) ⟫ʷ
wl0275 c4 = lw4 c4 (Toff012 ∷ Toff023 ∷ []) (Toff023 ∷ Toff012 ∷ []) tt tt Eq.refl

wl0276 : Complete 4 → ⟪ (CX31 ∷ Toff023 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
wl0276 c4 = lw4 c4 (CX31 ∷ Toff023 ∷ Toff023 ∷ []) (CX31 ∷ []) tt tt Eq.refl

wl0277 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ234 ∷ CX31 ∷ []) ⟫ʷ
wl0277 c4 = lw0 c4 (CCZ234 ∷ []) (CX31 ∷ CCZ234 ∷ CX31 ∷ []) tt tt Eq.refl

wl0278 : Complete 4 → ⟪ (CX13 ∷ CX31 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Sw13 ∷ []) ⟫ʷ
wl0278 c4 = lw4 c4 (CX13 ∷ CX31 ∷ CX13 ∷ []) (Sw13 ∷ []) tt tt Eq.refl

wl0279 : Complete 4 → ⟪ (CCZ124 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) ⟫ʷ
wl0279 c4 = lw0 c4 (CCZ124 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0280 : Complete 4 → ⟪ (CCZ124 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ124 ∷ []) ⟫ʷ
wl0280 c4 = lw0 c4 (CCZ124 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0281 : Complete 4 → ⟪ (CCZ234 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) ⟫ʷ
wl0281 c4 = lw0 c4 (CCZ234 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0282 : Complete 4 → ⟪ (CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wl0282 c4 = lw0 c4 (CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wl0283 : Complete 4 → ⟪ (CCZ023 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Sw13 ∷ CCZ012 ∷ []) ⟫ʷ
wl0283 c4 = lw4 c4 (CCZ023 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0284 : Complete 4 → ⟪ (Sw13 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw13 ∷ []) ⟫ʷ
wl0284 c4 = lw4 c4 (Sw13 ∷ Toff012 ∷ []) (Toff023 ∷ Sw13 ∷ []) tt tt Eq.refl

wl0285 : Complete 4 → ⟪ (CCZ012 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Sw13 ∷ CCZ023 ∷ []) ⟫ʷ
wl0285 c4 = lw4 c4 (CCZ012 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0286 : Complete 4 → ⟪ (Sw13 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Sw13 ∷ []) ⟫ʷ
wl0286 c4 = lw4 c4 (Sw13 ∷ Toff203 ∷ []) (Toff201 ∷ Sw13 ∷ []) tt tt Eq.refl

wl0287 : Complete 4 → ⟪ (Sw13 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0287 c4 = lw4 c4 (Sw13 ∷ Sw13 ∷ []) [] tt tt Eq.refl

wl0288 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) ⟫ʷ
wl0288 c4 = lw4 c4 (CCZ012 ∷ []) (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) tt tt Eq.refl

wl0289 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) ⟫ʷ
wl0289 c4 = lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl

wl0290 : Complete 4 → ⟪ (CCZ013 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) ⟫ʷ
wl0290 c4 = lw4 c4 (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) tt tt Eq.refl

wl0291 : Complete 4 → ⟪ (CCZ013 ∷ CZ13 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ []) ⟫ʷ
wl0291 c4 = lw4 c4 (CCZ013 ∷ CZ13 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ []) tt tt Eq.refl

wl0292 : Complete 4 → ⟪ (CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
wl0292 c4 = lw4 c4 (CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl

wl0293 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) ⟫ʷ
wl0293 c4 = lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) tt tt Eq.refl

wl0294 : Complete 4 → ⟪ (CCZ012 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ012 ∷ []) ⟫ʷ
wl0294 c4 = lw4 c4 (CCZ012 ∷ CS23 ∷ []) (CS23 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0295 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ234 ∷ CX41 ∷ []) ⟫ʷ
wl0295 c4 = lw0 c4 (CCZ234 ∷ []) (CX41 ∷ CCZ234 ∷ CX41 ∷ []) tt tt Eq.refl

wl0296 : Complete 4 → ⟪ (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ012 ∷ []) ⟫ʷ
wl0296 c4 = lw4 c4 (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) (Toff013 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0297 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) ⟫ʷ
wl0297 c4 = lw4 c4 (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) tt tt Eq.refl

wl0298 : Complete 4 → ⟪ (CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ
wl0298 c4 = lw4 c4 (CCZ012 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0299 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ123 ∷ CX14 ∷ []) ⟫ʷ
wl0299 c4 = lw0 c4 (CCZ123 ∷ []) (CX14 ∷ CCZ123 ∷ CX14 ∷ []) tt tt Eq.refl

wl0300 : Complete 4 → ⟪ (CX41 ∷ CX14 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ []) ⟫ʷ
wl0300 c4 = lw0 c4 (CX41 ∷ CX14 ∷ CX41 ∷ []) (Sw14 ∷ []) tt tt Eq.refl

wl0301 : Complete 4 → ⟪ (CCZ234 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) ⟫ʷ
wl0301 c4 = lw0 c4 (CCZ234 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0302 : Complete 4 → ⟪ (CCZ234 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ234 ∷ []) ⟫ʷ
wl0302 c4 = lw0 c4 (CCZ234 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0303 : Complete 4 → ⟪ (CCZ123 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) ⟫ʷ
wl0303 c4 = lw0 c4 (CCZ123 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0304 : Complete 4 → ⟪ (CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
wl0304 c4 = lw0 c4 (CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl

wl0305 : Complete 4 → ⟪ (CCZ234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0305 c4 = lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl

wl0306 : Complete 4 → ⟪ (Sw14 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0306 c4 = lw0 c4 (Sw14 ∷ Sw14 ∷ []) [] tt tt Eq.refl

wl0307 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) ⟫ʷ
wl0307 c4 = lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) tt tt Eq.refl

wl0308 : Complete 4 → ⟪ (CCZ023 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) ⟫ʷ
wl0308 c4 = lw4 c4 (CCZ023 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) tt tt Eq.refl

wl0309 : Complete 4 → ⟪ (CCZ023 ∷ CZ23 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ []) ⟫ʷ
wl0309 c4 = lw4 c4 (CCZ023 ∷ CZ23 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ []) tt tt Eq.refl

wl0310 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) ⟫ʷ
wl0310 c4 = lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl

wl0311 : Complete 4 → ⟪ (CCZ012 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ012 ∷ []) ⟫ʷ
wl0311 c4 = lw4 c4 (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0312 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CCZ134 ∷ CX42 ∷ []) ⟫ʷ
wl0312 c4 = lw0 c4 (CCZ134 ∷ []) (CX42 ∷ CCZ134 ∷ CX42 ∷ []) tt tt Eq.refl

wl0313 : Complete 4 → ⟪ (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ012 ∷ []) ⟫ʷ
wl0313 c4 = lw4 c4 (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) (Toff023 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0314 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) ⟫ʷ
wl0314 c4 = lw4 c4 (CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) tt tt Eq.refl

wl0315 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ CCZ123 ∷ CX24 ∷ []) ⟫ʷ
wl0315 c4 = lw0 c4 (CCZ123 ∷ []) (CX24 ∷ CCZ123 ∷ CX24 ∷ []) tt tt Eq.refl

wl0316 : Complete 4 → ⟪ (CX42 ∷ CX24 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ []) ⟫ʷ
wl0316 c4 = lw0 c4 (CX42 ∷ CX24 ∷ CX42 ∷ []) (Sw24 ∷ []) tt tt Eq.refl

wl0317 : Complete 4 → ⟪ (CCZ134 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) ⟫ʷ
wl0317 c4 = lw0 c4 (CCZ134 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0318 : Complete 4 → ⟪ (CCZ134 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CCZ134 ∷ []) ⟫ʷ
wl0318 c4 = lw0 c4 (CCZ134 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0319 : Complete 4 → ⟪ (CCZ123 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) ⟫ʷ
wl0319 c4 = lw0 c4 (CCZ123 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0320 : Complete 4 → ⟪ (CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wl0320 c4 = lw0 c4 (CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wl0321 : Complete 4 → ⟪ (CCZ134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0321 c4 = lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl

wl0322 : Complete 4 → ⟪ (Sw24 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0322 c4 = lw0 c4 (Sw24 ∷ Sw24 ∷ []) [] tt tt Eq.refl

wl0323 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) ⟫ʷ
wl0323 c4 = lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl

wl0324 : Complete 4 → ⟪ (CCZ013 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ013 ∷ []) ⟫ʷ
wl0324 c4 = lw4 c4 (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0325 : Complete 4 → ⟪ (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ013 ∷ []) ⟫ʷ
wl0325 c4 = lw4 c4 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (Toff012 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0326 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) ⟫ʷ
wl0326 c4 = lw4 c4 (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) tt tt Eq.refl

wl0327 : Complete 4 → ⟪ (CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ013 ∷ []) ⟫ʷ
wl0327 c4 = lw4 c4 (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0328 : Complete 4 → ⟪ (CCZ012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wl0328 c4 = lw4 c4 (CCZ012 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0329 : Complete 4 → ⟪ (CCZ012 ∷ CX31 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ012 ∷ []) ⟫ʷ
wl0329 c4 = lw4 c4 (CCZ012 ∷ CX31 ∷ CCZ023 ∷ []) (CX31 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0330 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) ⟫ʷ
wl0330 c4 = lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) tt tt Eq.refl

wl0331 : Complete 4 → ⟪ (CCZ012 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wl0331 c4 = lw4 c4 (CCZ012 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0332 : Complete 4 → ⟪ (CCZ012 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ012 ∷ []) ⟫ʷ
wl0332 c4 = lw4 c4 (CCZ012 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0333 : Complete 4 → ⟪ (CX31 ∷ CCZ023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
wl0333 c4 = lw4 c4 (CX31 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX31 ∷ []) tt tt Eq.refl

wl0334 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) ⟫ʷ
wl0334 c4 = lw0 c4 (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) tt tt Eq.refl

wl0335 : Complete 4 → ⟪ (CX31 ∷ CX13 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Sw13 ∷ []) ⟫ʷ
wl0335 c4 = lw4 c4 (CX31 ∷ CX13 ∷ CX31 ∷ []) (Sw13 ∷ []) tt tt Eq.refl

wl0336 : Complete 4 → ⟪ (CCZ234 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ234 ∷ []) ⟫ʷ
wl0336 c4 = lw0 c4 (CCZ234 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0337 : Complete 4 → ⟪ (CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
wl0337 c4 = lw0 c4 (CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl

wl0338 : Complete 4 → ⟪ (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
wl0338 c4 = lw4 c4 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0339 : Complete 4 → ⟪ (CCZ012 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ
wl0339 c4 = lw4 c4 (CCZ012 ∷ CZ12 ∷ []) (Toff012 ∷ CCZ012 ∷ Toff012 ∷ []) tt tt Eq.refl

wl0340 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ012 ∷ CZ12 ∷ []) ⟫ʷ
wl0340 c4 = lw4 c4 (CCZ012 ∷ []) (CZ12 ∷ CCZ012 ∷ CZ12 ∷ []) tt tt Eq.refl

wl0341 : Complete 4 → ⟪ (CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0341 c4 = lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl

wl0342 : Complete 4 → ⟪ (CCZ013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wl0342 c4 = lw4 c4 (CCZ013 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0343 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) ⟫ʷ
wl0343 c4 = lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl

wl0344 : Complete 4 → ⟪ (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
wl0344 c4 = lw4 c4 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl

wl0345 : Complete 4 → ⟪ (CCZ012 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Toff012 ∷ []) ⟫ʷ
wl0345 c4 = lw4 c4 (CCZ012 ∷ K0 ∷ []) (K0 ∷ Toff012 ∷ []) tt tt Eq.refl

wl0346 : Complete 4 → ⟪ (CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff012 ∷ []) ⟫ʷ
wl0346 c4 = lw4 c4 (CCZ012 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff012 ∷ []) tt tt Eq.refl

wl0347 : Complete 4 → ⟪ (S0 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wl0347 c4 = lw4 c4 (S0 ∷ Toff012 ∷ []) (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0348 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ
wl0348 c4 = lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl

wl0349 : Complete 4 → ⟪ (CS12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS12 ∷ []) ⟫ʷ
wl0349 c4 = lw4 c4 (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) tt tt Eq.refl

wl0350 : Complete 4 → ⟪ (S0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
wl0350 c4 = lw4 c4 (S0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (S0 ∷ []) tt tt Eq.refl

wl0351 : Complete 4 → ⟪ (S0⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wl0351 c4 = lw4 c4 (S0⁻ ∷ Toff012 ∷ []) (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0352 : Complete 4 → ⟪ (CS12⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0352 c4 = lw4 c4 (CS12⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0353 : Complete 4 → ⟪ (S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ []) ⟫ʷ
wl0353 c4 = lw4 c4 (S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) (S0⁻ ∷ []) tt tt Eq.refl

wl0354 : Complete 4 → ⟪ (CS01 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wl0354 c4 = lw4 c4 (CS01 ∷ Toff012 ∷ []) (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0355 : Complete 4 → ⟪ (CS01 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
wl0355 c4 = lw4 c4 (CS01 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (CS01 ∷ []) tt tt Eq.refl

wl0356 : Complete 4 → ⟪ (CS01⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wl0356 c4 = lw4 c4 (CS01⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0357 : Complete 4 → ⟪ (CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
wl0357 c4 = lw4 c4 (CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl

wl0358 : Complete 4 → ⟪ (CZ01 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ01 ∷ CZ12 ∷ []) ⟫ʷ
wl0358 c4 = lw4 c4 (CZ01 ∷ Toff012 ∷ []) (Toff012 ∷ CZ01 ∷ CZ12 ∷ []) tt tt Eq.refl

wl0359 : Complete 4 → ⟪ (CZ12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ12 ∷ []) ⟫ʷ
wl0359 c4 = lw4 c4 (CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ []) tt tt Eq.refl

wl0360 : Complete 4 → ⟪ (CZ01 ∷ CZ12 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ []) ⟫ʷ
wl0360 c4 = lw4 c4 (CZ01 ∷ CZ12 ∷ CZ12 ∷ []) (CZ01 ∷ []) tt tt Eq.refl

wl0361 : Complete 4 → ⟪ (CX10 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CX10 ∷ []) ⟫ʷ
wl0361 c4 = lw4 c4 (CX10 ∷ Toff012 ∷ []) (Toff012 ∷ CX10 ∷ []) tt tt Eq.refl

wl0362 : Complete 4 → ⟪ (CK10 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0362 c4 = lw4 c4 (CK10 ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0363 : Complete 4 → ⟪ (CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ K0⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ []) ⟫ʷ
wl0363 c4 = lw4 c4 (CK10⁻ ∷ []) (CS01 ∷ K0⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ []) tt tt Eq.refl

wl0364 : Complete 4 → ⟪ (S0 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wl0364 c4 = lw4 c4 (S0 ∷ CS01⁻ ∷ []) (X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl

wl0365 : Complete 4 → ⟪ (S0⁻ ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wl0365 c4 = lw4 c4 (S0⁻ ∷ CS01 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl

wl0366 : Complete 4 → ⟪ (K0 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wl0366 c4 = lw4 c4 (K0 ∷ CK10⁻ ∷ []) (X1 ∷ CK10 ∷ X1 ∷ []) tt tt Eq.refl

wl0367 : Complete 4 → ⟪ (K0⁻ ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wl0367 c4 = lw4 c4 (K0⁻ ∷ CK10 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl

wl0368 : Complete 4 → ⟪ (CS02 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wl0368 c4 = lw4 c4 (CS02 ∷ Toff012 ∷ []) (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0369 : Complete 4 → ⟪ (CS02 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
wl0369 c4 = lw4 c4 (CS02 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (CS02 ∷ []) tt tt Eq.refl

wl0370 : Complete 4 → ⟪ (CS02⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wl0370 c4 = lw4 c4 (CS02⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0371 : Complete 4 → ⟪ (CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wl0371 c4 = lw4 c4 (CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) (CS02⁻ ∷ []) tt tt Eq.refl

wl0372 : Complete 4 → ⟪ (CZ02 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ02 ∷ CZ12 ∷ []) ⟫ʷ
wl0372 c4 = lw4 c4 (CZ02 ∷ Toff012 ∷ []) (Toff012 ∷ CZ02 ∷ CZ12 ∷ []) tt tt Eq.refl

wl0373 : Complete 4 → ⟪ (CZ02 ∷ CZ12 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
wl0373 c4 = lw4 c4 (CZ02 ∷ CZ12 ∷ CZ12 ∷ []) (CZ02 ∷ []) tt tt Eq.refl

wl0374 : Complete 4 → ⟪ (CX20 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CX20 ∷ []) ⟫ʷ
wl0374 c4 = lw4 c4 (CX20 ∷ Toff012 ∷ []) (Toff012 ∷ CX20 ∷ []) tt tt Eq.refl

wl0375 : Complete 4 → ⟪ (CK20 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ K0⁻ ∷ CS02⁻ ∷ K0 ∷ CS02⁻ ∷ []) ⟫ʷ
wl0375 c4 = lw4 c4 (CK20 ∷ []) (CS02⁻ ∷ K0⁻ ∷ CS02⁻ ∷ K0 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl0376 : Complete 4 → ⟪ (CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ K0⁻ ∷ CS02 ∷ K0 ∷ CS02 ∷ []) ⟫ʷ
wl0376 c4 = lw4 c4 (CK20⁻ ∷ []) (CS02 ∷ K0⁻ ∷ CS02 ∷ K0 ∷ CS02 ∷ []) tt tt Eq.refl

wl0377 : Complete 4 → ⟪ (S0 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wl0377 c4 = lw4 c4 (S0 ∷ CS02⁻ ∷ []) (X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl

wl0378 : Complete 4 → ⟪ (S0⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wl0378 c4 = lw4 c4 (S0⁻ ∷ CS02 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl

wl0379 : Complete 4 → ⟪ (K0 ∷ CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wl0379 c4 = lw4 c4 (K0 ∷ CK20⁻ ∷ []) (X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl

wl0380 : Complete 4 → ⟪ (K0⁻ ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wl0380 c4 = lw4 c4 (K0⁻ ∷ CK20 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl

wl0381 : Complete 4 → ⟪ (CCZ012 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ012 ∷ []) ⟫ʷ
wl0381 c4 = lw4 c4 (CCZ012 ∷ CX03 ∷ []) (CX03 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0382 : Complete 4 → ⟪ (CCZ012 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CCZ012 ∷ []) ⟫ʷ
wl0382 c4 = lw4 c4 (CCZ012 ∷ CZ03 ∷ []) (CZ03 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0383 : Complete 4 → ⟪ (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ012 ∷ []) ⟫ʷ
wl0383 c4 = lw4 c4 (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) (CX30 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0384 : Complete 4 → ⟪ (CX30 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
wl0384 c4 = lw4 c4 (CX30 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX30 ∷ []) tt tt Eq.refl

wl0385 : Complete 4 → ⟪ (CK30 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ K0⁻ ∷ CS03⁻ ∷ K0 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0385 c4 = lw4 c4 (CK30 ∷ []) (CS03⁻ ∷ K0⁻ ∷ CS03⁻ ∷ K0 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0386 : Complete 4 → ⟪ (CK30⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ K0⁻ ∷ CS03 ∷ K0 ∷ CS03 ∷ []) ⟫ʷ
wl0386 c4 = lw4 c4 (CK30⁻ ∷ []) (CS03 ∷ K0⁻ ∷ CS03 ∷ K0 ∷ CS03 ∷ []) tt tt Eq.refl

wl0387 : Complete 4 → ⟪ (S0 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
wl0387 c4 = lw4 c4 (S0 ∷ CS03⁻ ∷ []) (X3 ∷ CS03 ∷ X3 ∷ []) tt tt Eq.refl

wl0388 : Complete 4 → ⟪ (S0⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
wl0388 c4 = lw4 c4 (S0⁻ ∷ CS03 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ []) tt tt Eq.refl

wl0389 : Complete 4 → ⟪ (K0 ∷ CK30⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
wl0389 c4 = lw4 c4 (K0 ∷ CK30⁻ ∷ []) (X3 ∷ CK30 ∷ X3 ∷ []) tt tt Eq.refl

wl0390 : Complete 4 → ⟪ (K0⁻ ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
wl0390 c4 = lw4 c4 (K0⁻ ∷ CK30 ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ []) tt tt Eq.refl

wl0391 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) ⟫ʷ
wl0391 c4 = lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl

wl0392 : Complete 4 → ⟪ (CCZ134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ134 ∷ []) ⟫ʷ
wl0392 c4 = lw0 c4 (CCZ134 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0393 : Complete 4 → ⟪ (CCZ134 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ134 ∷ []) ⟫ʷ
wl0393 c4 = lw0 c4 (CCZ134 ∷ CS12 ∷ []) (CS12 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0394 : Complete 4 → ⟪ (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ []) ⟫ʷ
wl0394 c4 = lw4 c4 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) tt tt Eq.refl

wl0395 : Complete 4 → ⟪ (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ []) ⟫ʷ
wl0395 c4 = lw0 c4 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl

wl0396 : Complete 4 → ⟪ (K1⁻ ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0396 c4 = lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl

wl0397 : Complete 4 → ⟪ (CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CCZ012 ∷ []) ⟫ʷ
wl0397 c4 = lw4 c4 (CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ []) (Toff102 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0398 : Complete 4 → ⟪ (CS34⁻ ∷ S1 ∷ Toff134 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ134 ∷ []) ⟫ʷ
wl0398 c4 = lw0 c4 (CS34⁻ ∷ S1 ∷ Toff134 ∷ S1⁻ ∷ []) (Toff134 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0399 : Complete 4 → ⟪ (S1⁻ ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0399 c4 = lw4 c4 (S1⁻ ∷ S1 ∷ []) [] tt tt Eq.refl

wl0400 : Complete 4 → ⟪ (CS02⁻ ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS02⁻ ∷ []) ⟫ʷ
wl0400 c4 = lw4 c4 (CS02⁻ ∷ S1 ∷ []) (S1 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl0401 : Complete 4 → ⟪ (CS02⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wl0401 c4 = lw4 c4 (CS02⁻ ∷ S1⁻ ∷ []) (S1⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl0402 : Complete 4 → ⟪ (Toff134 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0402 c4 = lw0 c4 (Toff134 ∷ Toff134 ∷ []) [] tt tt Eq.refl

wl0403 : Complete 4 → ⟪ (Toff102 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0403 c4 = lw4 c4 (Toff102 ∷ Toff102 ∷ []) [] tt tt Eq.refl

wl0404 : Complete 4 → ⟪ (CCZ012 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ
wl0404 c4 = lw4 c4 (CCZ012 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0405 : Complete 4 → ⟪ (CX24 ∷ CX42 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ []) ⟫ʷ
wl0405 c4 = lw0 c4 (CX24 ∷ CX42 ∷ CX24 ∷ []) (Sw24 ∷ []) tt tt Eq.refl

wl0406 : Complete 4 → ⟪ (CCZ123 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ CCZ123 ∷ []) ⟫ʷ
wl0406 c4 = lw0 c4 (CCZ123 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0407 : Complete 4 → ⟪ (CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wl0407 c4 = lw0 c4 (CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl

wl0408 : Complete 4 → ⟪ (CCZ123 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ123 ∷ CCZ234 ∷ []) ⟫ʷ
wl0408 c4 = lw0 c4 (CCZ123 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0409 : Complete 4 → ⟪ (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ []) ⟫ʷ
wl0409 c4 = lw4 c4 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl

wl0410 : Complete 4 → ⟪ (CS23⁻ ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS23⁻ ∷ []) ⟫ʷ
wl0410 c4 = lw0 c4 (CS23⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS23⁻ ∷ []) tt tt Eq.refl

wl0411 : Complete 4 → ⟪ (CCZ012 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ012 ∷ []) ⟫ʷ
wl0411 c4 = lw4 c4 (CCZ012 ∷ CX23 ∷ []) (CX23 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0412 : Complete 4 → ⟪ (Toff023 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ []) ⟫ʷ
wl0412 c4 = lw4 c4 (Toff023 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff023 ∷ []) tt tt Eq.refl

wl0413 : Complete 4 → ⟪ (CCZ234 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ234 ∷ []) ⟫ʷ
wl0413 c4 = lw0 c4 (CCZ234 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0414 : Complete 4 → ⟪ (CCZ234 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ234 ∷ []) ⟫ʷ
wl0414 c4 = lw0 c4 (CCZ234 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0415 : Complete 4 → ⟪ (CCZ234 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ234 ∷ []) ⟫ʷ
wl0415 c4 = lw0 c4 (CCZ234 ∷ CS12 ∷ []) (CS12 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0416 : Complete 4 → ⟪ (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
wl0416 c4 = lw4 c4 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (Toff201 ∷ []) tt tt Eq.refl

wl0417 : Complete 4 → ⟪ (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ []) ⟫ʷ
wl0417 c4 = lw0 c4 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl

wl0418 : Complete 4 → ⟪ (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
wl0418 c4 = lw4 c4 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff201 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0419 : Complete 4 → ⟪ (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ []) ⟫ʷ
wl0419 c4 = lw0 c4 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0420 : Complete 4 → ⟪ (Toff234 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0420 c4 = lw0 c4 (Toff234 ∷ Toff234 ∷ []) [] tt tt Eq.refl

wl0421 : Complete 4 → ⟪ (Toff201 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0421 c4 = lw4 c4 (Toff201 ∷ Toff201 ∷ []) [] tt tt Eq.refl

wl0422 : Complete 4 → ⟪ (CCZ012 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ
wl0422 c4 = lw4 c4 (CCZ012 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0423 : Complete 4 → ⟪ (CX14 ∷ CX41 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ []) ⟫ʷ
wl0423 c4 = lw0 c4 (CX14 ∷ CX41 ∷ CX14 ∷ []) (Sw14 ∷ []) tt tt Eq.refl

wl0424 : Complete 4 → ⟪ (CCZ123 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ123 ∷ []) ⟫ʷ
wl0424 c4 = lw0 c4 (CCZ123 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0425 : Complete 4 → ⟪ (CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wl0425 c4 = lw0 c4 (CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl

wl0426 : Complete 4 → ⟪ (CCZ123 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ123 ∷ CCZ134 ∷ []) ⟫ʷ
wl0426 c4 = lw0 c4 (CCZ123 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0427 : Complete 4 → ⟪ (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ []) ⟫ʷ
wl0427 c4 = lw4 c4 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl

wl0428 : Complete 4 → ⟪ (CS13⁻ ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0428 c4 = lw0 c4 (CS13⁻ ∷ Toff234 ∷ []) (Toff234 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0429 : Complete 4 → ⟪ (CS13 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CS13 ∷ []) ⟫ʷ
wl0429 c4 = lw0 c4 (CS13 ∷ Toff234 ∷ []) (Toff234 ∷ CS13 ∷ []) tt tt Eq.refl

wl0430 : Complete 4 → ⟪ (Toff013 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ []) ⟫ʷ
wl0430 c4 = lw4 c4 (Toff013 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff013 ∷ []) tt tt Eq.refl

wl0431 : Complete 4 → ⟪ (CCZ134 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ134 ∷ []) ⟫ʷ
wl0431 c4 = lw0 c4 (CCZ134 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0432 : Complete 4 → ⟪ (CCZ234 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ234 ∷ []) ⟫ʷ
wl0432 c4 = lw0 c4 (CCZ234 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0433 : Complete 4 → ⟪ (CCZ234 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ234 ∷ []) ⟫ʷ
wl0433 c4 = lw0 c4 (CCZ234 ∷ CS13 ∷ []) (CS13 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0434 : Complete 4 → ⟪ (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ []) ⟫ʷ
wl0434 c4 = lw4 c4 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (Toff301 ∷ []) tt tt Eq.refl

wl0435 : Complete 4 → ⟪ (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
wl0435 c4 = lw0 c4 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl

wl0436 : Complete 4 → ⟪ (K3⁻ ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0436 c4 = lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl

wl0437 : Complete 4 → ⟪ (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ []) ⟫ʷ
wl0437 c4 = lw4 c4 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0438 : Complete 4 → ⟪ (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
wl0438 c4 = lw0 c4 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0439 : Complete 4 → ⟪ (CS24⁻ ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS24⁻ ∷ []) ⟫ʷ
wl0439 c4 = lw0 c4 (CS24⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0440 : Complete 4 → ⟪ (CS24⁻ ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0440 c4 = lw0 c4 (CS24⁻ ∷ S3 ∷ []) (S3 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0441 : Complete 4 → ⟪ (S3⁻ ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0441 c4 = lw4 c4 (S3⁻ ∷ S3 ∷ []) [] tt tt Eq.refl

wl0442 : Complete 4 → ⟪ (Toff324 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0442 c4 = lw0 c4 (Toff324 ∷ Toff324 ∷ []) [] tt tt Eq.refl

wl0443 : Complete 4 → ⟪ (Toff301 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0443 c4 = lw4 c4 (Toff301 ∷ Toff301 ∷ []) [] tt tt Eq.refl

wl0444 : Complete 4 → ⟪ (CCZ013 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ CCZ013 ∷ []) ⟫ʷ
wl0444 c4 = lw4 c4 (CCZ013 ∷ CX02 ∷ []) (CX02 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0445 : Complete 4 → ⟪ (CCZ123 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) ⟫ʷ
wl0445 c4 = lw0 c4 (CCZ123 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0446 : Complete 4 → ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wl0446 c4 = lw4 c4 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl

wl0447 : Complete 4 → ⟪ (CS12⁻ ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0447 c4 = lw0 c4 (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0448 : Complete 4 → ⟪ (CCZ013 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ013 ∷ []) ⟫ʷ
wl0448 c4 = lw4 c4 (CCZ013 ∷ CX12 ∷ []) (CX12 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0449 : Complete 4 → ⟪ (Toff012 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wl0449 c4 = lw4 c4 (Toff012 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff012 ∷ []) tt tt Eq.refl

wl0450 : Complete 4 → ⟪ (CCZ124 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ124 ∷ []) ⟫ʷ
wl0450 c4 = lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0451 : Complete 4 → ⟪ (CCZ234 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CCZ234 ∷ []) ⟫ʷ
wl0451 c4 = lw0 c4 (CCZ234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0452 : Complete 4 → ⟪ (CCZ234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ234 ∷ []) ⟫ʷ
wl0452 c4 = lw0 c4 (CCZ234 ∷ CS14 ∷ []) (CS14 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0453 : Complete 4 → ⟪ (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ []) ⟫ʷ
wl0453 c4 = lw0 c4 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) tt tt Eq.refl

wl0454 : Complete 4 → ⟪ (K4⁻ ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0454 c4 = lw0 c4 (K4⁻ ∷ K4 ∷ []) [] tt tt Eq.refl

wl0455 : Complete 4 → ⟪ (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ234 ∷ []) ⟫ʷ
wl0455 c4 = lw0 c4 (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) (Toff423 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0456 : Complete 4 → ⟪ (S4⁻ ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0456 c4 = lw0 c4 (S4⁻ ∷ S4 ∷ []) [] tt tt Eq.refl

wl0457 : Complete 4 → ⟪ (Toff423 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0457 c4 = lw0 c4 (Toff423 ∷ Toff423 ∷ []) [] tt tt Eq.refl

wl0458 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) ⟫ʷ
wl0458 c4 = lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) tt tt Eq.refl

wl0459 : Complete 4 → ⟪ (CCZ124 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ123 ∷ CCZ124 ∷ []) ⟫ʷ
wl0459 c4 = lw0 c4 (CCZ124 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0460 : Complete 4 → ⟪ (CS12⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0460 c4 = lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0461 : Complete 4 → ⟪ (CS12 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS12 ∷ []) ⟫ʷ
wl0461 c4 = lw0 c4 (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) tt tt Eq.refl

wl0462 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) ⟫ʷ
wl0462 c4 = lw0 c4 (CCZ123 ∷ []) (CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0463 : Complete 4 → ⟪ (CCZ123 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ123 ∷ []) ⟫ʷ
wl0463 c4 = lw0 c4 (CCZ123 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0464 : Complete 4 → ⟪ (CCZ123 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ123 ∷ []) ⟫ʷ
wl0464 c4 = lw4 c4 (CCZ123 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0465 : Complete 4 → ⟪ (CCZ124 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ CZ12 ∷ []) ⟫ʷ
wl0465 c4 = lw0 c4 (CCZ124 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ124 ∷ CZ12 ∷ []) tt tt Eq.refl

wl0466 : Complete 4 → ⟪ (CCZ124 ∷ CZ12 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ []) ⟫ʷ
wl0466 c4 = lw0 c4 (CCZ124 ∷ CZ12 ∷ Toff412 ∷ CCZ124 ∷ []) (Toff412 ∷ []) tt tt Eq.refl

wl0467 : Complete 4 → ⟪ (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ []) ⟫ʷ
wl0467 c4 = lw0 c4 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (Toff412 ∷ []) tt tt Eq.refl

wl0468 : Complete 4 → ⟪ (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
wl0468 c4 = lw0 c4 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (Toff412 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0469 : Complete 4 → ⟪ (CS03⁻ ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
wl0469 c4 = lw4 c4 (CS03⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0470 : Complete 4 → ⟪ (Toff412 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0470 c4 = lw0 c4 (Toff412 ∷ Toff412 ∷ []) [] tt tt Eq.refl

wl0471 : Complete 4 → ⟪ (CCZ124 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ124 ∷ []) ⟫ʷ
wl0471 c4 = lw0 c4 (CCZ124 ∷ CS34 ∷ []) (CS34 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0472 : Complete 4 → ⟪ (CX34 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CX34 ∷ []) ⟫ʷ
wl0472 c4 = lw0 c4 (CX34 ∷ Toff412 ∷ []) (Toff412 ∷ CX34 ∷ []) tt tt Eq.refl

wl0473 : Complete 4 → ⟪ (CCZ123 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) ⟫ʷ
wl0473 c4 = lw4 c4 (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) tt tt Eq.refl

wl0474 : Complete 4 → ⟪ (CCZ123 ∷ CZ12 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wl0474 c4 = lw4 c4 (CCZ123 ∷ CZ12 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ []) tt tt Eq.refl

wl0475 : Complete 4 → ⟪ (CCZ234 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ234 ∷ CCZ123 ∷ []) ⟫ʷ
wl0475 c4 = lw0 c4 (CCZ234 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ234 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0476 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ123 ∷ CX20 ∷ []) ⟫ʷ
wl0476 c4 = lw4 c4 (CCZ123 ∷ []) (CX20 ∷ CCZ123 ∷ CX20 ∷ []) tt tt Eq.refl

wl0477 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) ⟫ʷ
wl0477 c4 = lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) tt tt Eq.refl

wl0478 : Complete 4 → ⟪ (CS13 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS13 ∷ []) ⟫ʷ
wl0478 c4 = lw0 c4 (CS13 ∷ Toff412 ∷ []) (Toff412 ∷ CS13 ∷ []) tt tt Eq.refl

wl0479 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ CCZ013 ∷ CX02 ∷ []) ⟫ʷ
wl0479 c4 = lw4 c4 (CCZ013 ∷ []) (CX02 ∷ CCZ013 ∷ CX02 ∷ []) tt tt Eq.refl

wl0480 : Complete 4 → ⟪ (CX20 ∷ CX02 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Sw02 ∷ []) ⟫ʷ
wl0480 c4 = lw4 c4 (CX20 ∷ CX02 ∷ CX20 ∷ []) (Sw02 ∷ []) tt tt Eq.refl

wl0481 : Complete 4 → ⟪ (CCZ123 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ
wl0481 c4 = lw4 c4 (CCZ123 ∷ CX02 ∷ []) (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0482 : Complete 4 → ⟪ (CCZ123 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ123 ∷ []) ⟫ʷ
wl0482 c4 = lw4 c4 (CCZ123 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0483 : Complete 4 → ⟪ (CCZ013 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) ⟫ʷ
wl0483 c4 = lw4 c4 (CCZ013 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0484 : Complete 4 → ⟪ (CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wl0484 c4 = lw4 c4 (CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl

wl0485 : Complete 4 → ⟪ (Sw02 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0485 c4 = lw4 c4 (Sw02 ∷ Sw02 ∷ []) [] tt tt Eq.refl

wl0486 : Complete 4 → ⟪ (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
wl0486 c4 = lw0 c4 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl

wl0487 : Complete 4 → ⟪ (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wl0487 c4 = lw4 c4 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl

wl0488 : Complete 4 → ⟪ (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ []) ⟫ʷ
wl0488 c4 = lw4 c4 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0489 : Complete 4 → ⟪ (Toff312 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0489 c4 = lw4 c4 (Toff312 ∷ Toff312 ∷ []) [] tt tt Eq.refl

wl0490 : Complete 4 → ⟪ (CCZ123 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ123 ∷ []) ⟫ʷ
wl0490 c4 = lw4 c4 (CCZ123 ∷ CS03 ∷ []) (CS03 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0491 : Complete 4 → ⟪ (CCZ123 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl0491 c4 = lw0 c4 (CCZ123 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0492 : Complete 4 → ⟪ (CCZ123 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ123 ∷ []) ⟫ʷ
wl0492 c4 = lw0 c4 (CCZ123 ∷ CS34 ∷ []) (CS34 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0493 : Complete 4 → ⟪ (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wl0493 c4 = lw4 c4 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl

wl0494 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) ⟫ʷ
wl0494 c4 = lw0 c4 (CCZ123 ∷ []) (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) tt tt Eq.refl

wl0495 : Complete 4 → ⟪ (CCZ123 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl0495 c4 = lw4 c4 (CCZ123 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0496 : Complete 4 → ⟪ (CCZ234 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ124 ∷ CCZ234 ∷ []) ⟫ʷ
wl0496 c4 = lw0 c4 (CCZ234 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0497 : Complete 4 → ⟪ (CCZ124 ∷ CCZ234 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ234 ∷ []) ⟫ʷ
wl0497 c4 = lw0 c4 (CCZ124 ∷ CCZ234 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0498 : Complete 4 → ⟪ (CCZ013 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ012 ∷ CCZ013 ∷ []) ⟫ʷ
wl0498 c4 = lw4 c4 (CCZ013 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0499 : Complete 4 → ⟪ (CS14 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS14 ∷ []) ⟫ʷ
wl0499 c4 = lw0 c4 (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) tt tt Eq.refl

wl0500 : Complete 4 → ⟪ (CS01⁻ ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS01⁻ ∷ []) ⟫ʷ
wl0500 c4 = lw4 c4 (CS01⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl0501 : Complete 4 → ⟪ (CS01 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS01 ∷ []) ⟫ʷ
wl0501 c4 = lw4 c4 (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) tt tt Eq.refl

wl0502 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ []) ⟫ʷ
wl0502 c4 = lw4 c4 (CCZ012 ∷ []) (CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0503 : Complete 4 → ⟪ (CCZ012 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ012 ∷ []) ⟫ʷ
wl0503 c4 = lw4 c4 (CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0504 : Complete 4 → ⟪ (CCZ123 ∷ CZ12 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ []) ⟫ʷ
wl0504 c4 = lw4 c4 (CCZ123 ∷ CZ12 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ []) tt tt Eq.refl

------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP03 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp0474 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0474 c4 = pw1 c4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0475 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wp0475 c4 = pw2 c4 (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wp0476 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wp0476 c4 = pw1 c4 (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wp0477 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wp0477 c4 = pw1 c4 (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wp0478 : Complete 4 → ⟪ (CCZ024 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0478 c4 = pw1 c4 (CCZ024 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0479 : Complete 4 → ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0479 c4 = pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0480 : Complete 4 → ⟪ (CS04 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ014 ∷ []) ⟫ʷ
wp0480 c4 = pw2 c4 (CS04 ∷ Toff014 ∷ []) (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0481 : Complete 4 → ⟪ (CS04 ∷ CS14 ∷ CCZ014 ∷ CS14 ∷ CZ14 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
wp0481 c4 = pw2 c4 (CS04 ∷ CS14 ∷ CCZ014 ∷ CS14 ∷ CZ14 ∷ CCZ014 ∷ []) (CS04 ∷ []) tt tt Eq.refl

wp0482 : Complete 4 → ⟪ (CCZ014 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Toff014 ∷ []) ⟫ʷ
wp0482 c4 = pw2 c4 (CCZ014 ∷ K0 ∷ []) (K0 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0483 : Complete 4 → ⟪ (CCZ014 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff014 ∷ []) ⟫ʷ
wp0483 c4 = pw2 c4 (CCZ014 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff014 ∷ []) tt tt Eq.refl

wp0484 : Complete 4 → ⟪ (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) ⟫ʷ
wp0484 c4 = pw1 c4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wp0485 : Complete 4 → ⟪ (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS13 ∷ []) ⟫ʷ
wp0485 c4 = pw2 c4 (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS13 ∷ []) tt tt Eq.refl

wp0486 : Complete 4 → ⟪ (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS13⁻ ∷ []) ⟫ʷ
wp0486 c4 = pw2 c4 (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0487 : Complete 4 → ⟪ (CS04 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ024 ∷ []) ⟫ʷ
wp0487 c4 = pw1 c4 (CS04 ∷ Toff024 ∷ []) (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0488 : Complete 4 → ⟪ (CS04 ∷ CS24 ∷ CCZ024 ∷ CS24 ∷ CZ24 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
wp0488 c4 = pw1 c4 (CS04 ∷ CS24 ∷ CCZ024 ∷ CS24 ∷ CZ24 ∷ CCZ024 ∷ []) (CS04 ∷ []) tt tt Eq.refl

wp0489 : Complete 4 → ⟪ (CCZ024 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Toff024 ∷ []) ⟫ʷ
wp0489 c4 = pw1 c4 (CCZ024 ∷ K0 ∷ []) (K0 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0490 : Complete 4 → ⟪ (CCZ024 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff024 ∷ []) ⟫ʷ
wp0490 c4 = pw1 c4 (CCZ024 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff024 ∷ []) tt tt Eq.refl

wp0491 : Complete 4 → ⟪ (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ []) ⟫ʷ
wp0491 c4 = pw2 c4 (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ []) tt tt Eq.refl

wp0492 : Complete 4 → ⟪ (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS12 ∷ []) ⟫ʷ
wp0492 c4 = pw3 c4 (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS12 ∷ []) tt tt Eq.refl

wp0493 : Complete 4 → ⟪ (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0493 c4 = pw3 c4 (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0494 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0494 c4 = pw2 c4 (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0495 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0495 c4 = pw2 c4 (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0496 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) ⟫ʷ
wp0496 c4 = pw3 c4 (CCZ024 ∷ []) (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) tt tt Eq.refl

wp0497 : Complete 4 → ⟪ (CX01 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX01 ∷ []) ⟫ʷ
wp0497 c4 = pw3 c4 (CX01 ∷ Toff204 ∷ []) (Toff204 ∷ CX01 ∷ []) tt tt Eq.refl

wp0498 : Complete 4 → ⟪ (CCZ023 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ023 ∷ CCZ034 ∷ []) ⟫ʷ
wp0498 c4 = pw1 c4 (CCZ023 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ023 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0499 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ034 ∷ CX01 ∷ []) ⟫ʷ
wp0499 c4 = pw2 c4 (CCZ034 ∷ []) (CX01 ∷ CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl

wp0500 : Complete 4 → ⟪ (CX10 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX10 ∷ Toff214 ∷ []) ⟫ʷ
wp0500 c4 = pw3 c4 (CX10 ∷ Toff204 ∷ []) (Toff204 ∷ CX10 ∷ Toff214 ∷ []) tt tt Eq.refl

wp0501 : Complete 4 → ⟪ (CS34 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS34 ∷ []) ⟫ʷ
wp0501 c4 = pw1 c4 (CS34 ∷ Toff204 ∷ []) (Toff204 ∷ CS34 ∷ []) tt tt Eq.refl

wp0502 : Complete 4 → ⟪ (CX41 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX41 ∷ []) ⟫ʷ
wp0502 c4 = pw3 c4 (CX41 ∷ Toff204 ∷ []) (Toff204 ∷ CX41 ∷ []) tt tt Eq.refl

wp0503 : Complete 4 → ⟪ (Toff204 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff204 ∷ []) ⟫ʷ
wp0503 c4 = pw3 c4 (Toff204 ∷ Toff214 ∷ []) (Toff214 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0504 : Complete 4 → ⟪ (CX10 ∷ Toff214 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wp0504 c4 = pw3 c4 (CX10 ∷ Toff214 ∷ Toff214 ∷ []) (CX10 ∷ []) tt tt Eq.refl

wp0505 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ134 ∷ CX10 ∷ []) ⟫ʷ
wp0505 c4 = pw2 c4 (CCZ134 ∷ []) (CX10 ∷ CCZ134 ∷ CX10 ∷ []) tt tt Eq.refl

wp0506 : Complete 4 → ⟪ (CCZ034 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) ⟫ʷ
wp0506 c4 = pw2 c4 (CCZ034 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0507 : Complete 4 → ⟪ (CCZ134 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ
wp0507 c4 = pw2 c4 (CCZ134 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0508 : Complete 4 → ⟪ (CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0508 c4 = pw2 c4 (CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0509 : Complete 4 → ⟪ (CCZ124 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ024 ∷ []) ⟫ʷ
wp0509 c4 = pw3 c4 (CCZ124 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0510 : Complete 4 → ⟪ (Sw01 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw01 ∷ []) ⟫ʷ
wp0510 c4 = pw3 c4 (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0511 : Complete 4 → ⟪ (CCZ024 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ124 ∷ []) ⟫ʷ
wp0511 c4 = pw3 c4 (CCZ024 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0512 : Complete 4 → ⟪ (Sw01 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw01 ∷ []) ⟫ʷ
wp0512 c4 = pw3 c4 (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0513 : Complete 4 → ⟪ (CCZ023 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ023 ∷ []) ⟫ʷ
wp0513 c4 = pw1 c4 (CCZ023 ∷ CS24 ∷ []) (CS24 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0514 : Complete 4 → ⟪ (CS03⁻ ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
wp0514 c4 = pw2 c4 (CS03⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0515 : Complete 4 → ⟪ (CCZ124 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ124 ∷ []) ⟫ʷ
wp0515 c4 = pw3 c4 (CCZ124 ∷ CS02 ∷ []) (CS02 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0516 : Complete 4 → ⟪ (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wp0516 c4 = pw3 c4 (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wp0517 : Complete 4 → ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0517 c4 = pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0518 : Complete 4 → ⟪ (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0518 c4 = pw2 c4 (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0519 : Complete 4 → ⟪ (CX43 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX43 ∷ []) ⟫ʷ
wp0519 c4 = pw1 c4 (CX43 ∷ Toff024 ∷ []) (Toff024 ∷ CX43 ∷ []) tt tt Eq.refl

wp0520 : Complete 4 → ⟪ (CCZ014 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ014 ∷ CCZ124 ∷ []) ⟫ʷ
wp0520 c4 = pw3 c4 (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0521 : Complete 4 → ⟪ (CCZ013 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wp0521 c4 = pw2 c4 (CCZ013 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0522 : Complete 4 → ⟪ (CX34 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX34 ∷ Toff023 ∷ []) ⟫ʷ
wp0522 c4 = pw1 c4 (CX34 ∷ Toff024 ∷ []) (Toff024 ∷ CX34 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0523 : Complete 4 → ⟪ (CCZ013 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ013 ∷ []) ⟫ʷ
wp0523 c4 = pw2 c4 (CCZ013 ∷ CX34 ∷ []) (CX34 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0524 : Complete 4 → ⟪ (CS12 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS12 ∷ []) ⟫ʷ
wp0524 c4 = pw3 c4 (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) tt tt Eq.refl

wp0525 : Complete 4 → ⟪ (CX23 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX23 ∷ []) ⟫ʷ
wp0525 c4 = pw1 c4 (CX23 ∷ Toff024 ∷ []) (Toff024 ∷ CX23 ∷ []) tt tt Eq.refl

wp0526 : Complete 4 → ⟪ (CX34 ∷ Toff023 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ []) ⟫ʷ
wp0526 c4 = pw1 c4 (CX34 ∷ Toff023 ∷ Toff023 ∷ []) (CX34 ∷ []) tt tt Eq.refl

wp0527 : Complete 4 → ⟪ (CCZ023 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ024 ∷ []) ⟫ʷ
wp0527 c4 = pw1 c4 (CCZ023 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0528 : Complete 4 → ⟪ (Sw34 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw34 ∷ []) ⟫ʷ
wp0528 c4 = pw1 c4 (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0529 : Complete 4 → ⟪ (CCZ024 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ023 ∷ []) ⟫ʷ
wp0529 c4 = pw1 c4 (CCZ024 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0530 : Complete 4 → ⟪ (Sw34 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw34 ∷ []) ⟫ʷ
wp0530 c4 = pw1 c4 (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0531 : Complete 4 → ⟪ (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) ⟫ʷ
wp0531 c4 = pw2 c4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0532 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0532 c4 = pw1 c4 (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0533 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0533 c4 = pw1 c4 (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0534 : Complete 4 → ⟪ (CS24 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) ⟫ʷ
wp0534 c4 = pw1 c4 (CS24 ∷ Toff204 ∷ []) (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0535 : Complete 4 → ⟪ (CS24 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ []) ⟫ʷ
wp0535 c4 = pw1 c4 (CS24 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) (CS24 ∷ []) tt tt Eq.refl

wp0536 : Complete 4 → ⟪ (CCZ024 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Toff204 ∷ []) ⟫ʷ
wp0536 c4 = pw1 c4 (CCZ024 ∷ K2 ∷ []) (K2 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0537 : Complete 4 → ⟪ (CCZ024 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Toff204 ∷ []) ⟫ʷ
wp0537 c4 = pw1 c4 (CCZ024 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff204 ∷ []) tt tt Eq.refl

wp0538 : Complete 4 → ⟪ (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS03 ∷ []) ⟫ʷ
wp0538 c4 = pw1 c4 (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0539 : Complete 4 → ⟪ (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0539 c4 = pw1 c4 (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0540 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) ⟫ʷ
wp0540 c4 = pw2 c4 (CCZ014 ∷ []) (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) tt tt Eq.refl

wp0541 : Complete 4 → ⟪ (CX12 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX12 ∷ []) ⟫ʷ
wp0541 c4 = pw3 c4 (CX12 ∷ Toff014 ∷ []) (Toff014 ∷ CX12 ∷ []) tt tt Eq.refl

wp0542 : Complete 4 → ⟪ (CCZ013 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ013 ∷ CCZ134 ∷ []) ⟫ʷ
wp0542 c4 = pw2 c4 (CCZ013 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ013 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0543 : Complete 4 → ⟪ (CCZ023 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ023 ∷ []) ⟫ʷ
wp0543 c4 = pw1 c4 (CCZ023 ∷ CS34 ∷ []) (CS34 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0544 : Complete 4 → ⟪ (CX21 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX21 ∷ Toff024 ∷ []) ⟫ʷ
wp0544 c4 = pw3 c4 (CX21 ∷ Toff014 ∷ []) (Toff014 ∷ CX21 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0545 : Complete 4 → ⟪ (CCZ023 ∷ Toff024 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ023 ∷ []) ⟫ʷ
wp0545 c4 = pw1 c4 (CCZ023 ∷ Toff024 ∷ CCZ234 ∷ []) (Toff024 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0546 : Complete 4 → ⟪ (CS34 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS34 ∷ []) ⟫ʷ
wp0546 c4 = pw2 c4 (CS34 ∷ Toff014 ∷ []) (Toff014 ∷ CS34 ∷ []) tt tt Eq.refl

wp0547 : Complete 4 → ⟪ (CX42 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX42 ∷ []) ⟫ʷ
wp0547 c4 = pw3 c4 (CX42 ∷ Toff014 ∷ []) (Toff014 ∷ CX42 ∷ []) tt tt Eq.refl

wp0548 : Complete 4 → ⟪ (Toff014 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff014 ∷ []) ⟫ʷ
wp0548 c4 = pw3 c4 (Toff014 ∷ Toff024 ∷ []) (Toff024 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0549 : Complete 4 → ⟪ (CX21 ∷ Toff024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wp0549 c4 = pw3 c4 (CX21 ∷ Toff024 ∷ Toff024 ∷ []) (CX21 ∷ []) tt tt Eq.refl

wp0550 : Complete 4 → ⟪ (CCZ023 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ023 ∷ []) ⟫ʷ
wp0550 c4 = pw1 c4 (CCZ023 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0551 : Complete 4 → ⟪ (CCZ024 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ014 ∷ []) ⟫ʷ
wp0551 c4 = pw3 c4 (CCZ024 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0552 : Complete 4 → ⟪ (Sw12 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw12 ∷ []) ⟫ʷ
wp0552 c4 = pw3 c4 (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) tt tt Eq.refl

wp0553 : Complete 4 → ⟪ (CCZ014 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ024 ∷ []) ⟫ʷ
wp0553 c4 = pw3 c4 (CCZ014 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0554 : Complete 4 → ⟪ (Sw12 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw12 ∷ []) ⟫ʷ
wp0554 c4 = pw3 c4 (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) tt tt Eq.refl

wp0555 : Complete 4 → ⟪ (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ []) ⟫ʷ
wp0555 c4 = pw1 c4 (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0556 : Complete 4 → ⟪ (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0556 c4 = pw1 c4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0557 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0557 c4 = pw1 c4 (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0558 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0558 c4 = pw1 c4 (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0559 : Complete 4 → ⟪ (CCZ234 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) ⟫ʷ
wp0559 c4 = pw1 c4 (CCZ234 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0560 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ034 ∷ CX41 ∷ []) ⟫ʷ
wp0560 c4 = pw2 c4 (CCZ034 ∷ []) (CX41 ∷ CCZ034 ∷ CX41 ∷ []) tt tt Eq.refl

wp0561 : Complete 4 → ⟪ (CX14 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX14 ∷ Toff201 ∷ []) ⟫ʷ
wp0561 c4 = pw3 c4 (CX14 ∷ Toff204 ∷ []) (Toff204 ∷ CX14 ∷ Toff201 ∷ []) tt tt Eq.refl

wp0562 : Complete 4 → ⟪ (CS03 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS03 ∷ []) ⟫ʷ
wp0562 c4 = pw1 c4 (CS03 ∷ Toff204 ∷ []) (Toff204 ∷ CS03 ∷ []) tt tt Eq.refl

wp0563 : Complete 4 → ⟪ (Toff201 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff201 ∷ []) ⟫ʷ
wp0563 c4 = pw3 c4 (Toff201 ∷ Toff204 ∷ []) (Toff204 ∷ Toff201 ∷ []) tt tt Eq.refl

wp0564 : Complete 4 → ⟪ (CX14 ∷ Toff201 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wp0564 c4 = pw3 c4 (CX14 ∷ Toff201 ∷ Toff201 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wp0565 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ013 ∷ CX14 ∷ []) ⟫ʷ
wp0565 c4 = pw2 c4 (CCZ013 ∷ []) (CX14 ∷ CCZ013 ∷ CX14 ∷ []) tt tt Eq.refl

wp0566 : Complete 4 → ⟪ (CCZ034 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) ⟫ʷ
wp0566 c4 = pw2 c4 (CCZ034 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0567 : Complete 4 → ⟪ (CCZ013 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) ⟫ʷ
wp0567 c4 = pw2 c4 (CCZ013 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0568 : Complete 4 → ⟪ (CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0568 c4 = pw2 c4 (CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0569 : Complete 4 → ⟪ (Sw14 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Sw14 ∷ []) ⟫ʷ
wp0569 c4 = pw3 c4 (Sw14 ∷ Toff204 ∷ []) (Toff201 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0570 : Complete 4 → ⟪ (Sw14 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw14 ∷ []) ⟫ʷ
wp0570 c4 = pw3 c4 (Sw14 ∷ Toff012 ∷ []) (Toff024 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0571 : Complete 4 → ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0571 c4 = pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0572 : Complete 4 → ⟪ (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CCZ023 ∷ []) ⟫ʷ
wp0572 c4 = pw1 c4 (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) (CX42 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0573 : Complete 4 → ⟪ (CCZ034 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ
wp0573 c4 = pw2 c4 (CCZ034 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0574 : Complete 4 → ⟪ (CCZ023 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wp0574 c4 = pw1 c4 (CCZ023 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0575 : Complete 4 → ⟪ (CCZ023 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ023 ∷ []) ⟫ʷ
wp0575 c4 = pw1 c4 (CCZ023 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0576 : Complete 4 → ⟪ (CX42 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ []) ⟫ʷ
wp0576 c4 = pw1 c4 (CX42 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX42 ∷ []) tt tt Eq.refl

wp0577 : Complete 4 → ⟪ (CX24 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX24 ∷ Toff012 ∷ []) ⟫ʷ
wp0577 c4 = pw3 c4 (CX24 ∷ Toff014 ∷ []) (Toff014 ∷ CX24 ∷ Toff012 ∷ []) tt tt Eq.refl

wp0578 : Complete 4 → ⟪ (CCZ023 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ CCZ023 ∷ []) ⟫ʷ
wp0578 c4 = pw1 c4 (CCZ023 ∷ CX24 ∷ []) (CX24 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0579 : Complete 4 → ⟪ (CS13 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS13 ∷ []) ⟫ʷ
wp0579 c4 = pw2 c4 (CS13 ∷ Toff014 ∷ []) (Toff014 ∷ CS13 ∷ []) tt tt Eq.refl

wp0580 : Complete 4 → ⟪ (Toff012 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff012 ∷ []) ⟫ʷ
wp0580 c4 = pw3 c4 (Toff012 ∷ Toff014 ∷ []) (Toff014 ∷ Toff012 ∷ []) tt tt Eq.refl

wp0581 : Complete 4 → ⟪ (CX24 ∷ Toff012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ []) ⟫ʷ
wp0581 c4 = pw3 c4 (CX24 ∷ Toff012 ∷ Toff012 ∷ []) (CX24 ∷ []) tt tt Eq.refl

wp0582 : Complete 4 → ⟪ (CCZ012 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ CCZ014 ∷ []) ⟫ʷ
wp0582 c4 = pw3 c4 (CCZ012 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0583 : Complete 4 → ⟪ (Sw24 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sw24 ∷ []) ⟫ʷ
wp0583 c4 = pw3 c4 (Sw24 ∷ Toff014 ∷ []) (Toff012 ∷ Sw24 ∷ []) tt tt Eq.refl

wp0584 : Complete 4 → ⟪ (CCZ014 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ CCZ012 ∷ []) ⟫ʷ
wp0584 c4 = pw3 c4 (CCZ014 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0585 : Complete 4 → ⟪ (Sw24 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw24 ∷ []) ⟫ʷ
wp0585 c4 = pw3 c4 (Sw24 ∷ Toff102 ∷ []) (Toff104 ∷ Sw24 ∷ []) tt tt Eq.refl

wp0586 : Complete 4 → ⟪ (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ []) ⟫ʷ
wp0586 c4 = pw1 c4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0587 : Complete 4 → ⟪ (CCZ012 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) ⟫ʷ
wp0587 c4 = pw3 c4 (CCZ012 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0588 : Complete 4 → ⟪ (CX32 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX32 ∷ Toff034 ∷ []) ⟫ʷ
wp0588 c4 = pw1 c4 (CX32 ∷ Toff024 ∷ []) (Toff024 ∷ CX32 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0589 : Complete 4 → ⟪ (CCZ013 ∷ Toff034 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ013 ∷ []) ⟫ʷ
wp0589 c4 = pw2 c4 (CCZ013 ∷ Toff034 ∷ CCZ134 ∷ []) (Toff034 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0590 : Complete 4 → ⟪ (CS14 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS14 ∷ []) ⟫ʷ
wp0590 c4 = pw3 c4 (CS14 ∷ Toff024 ∷ []) (Toff024 ∷ CS14 ∷ []) tt tt Eq.refl

wp0591 : Complete 4 → ⟪ (Toff024 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff024 ∷ []) ⟫ʷ
wp0591 c4 = pw1 c4 (Toff024 ∷ Toff034 ∷ []) (Toff034 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0592 : Complete 4 → ⟪ (CX32 ∷ Toff034 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
wp0592 c4 = pw1 c4 (CX32 ∷ Toff034 ∷ Toff034 ∷ []) (CX32 ∷ []) tt tt Eq.refl

wp0593 : Complete 4 → ⟪ (CCZ013 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ013 ∷ []) ⟫ʷ
wp0593 c4 = pw2 c4 (CCZ013 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0594 : Complete 4 → ⟪ (CCZ034 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ024 ∷ []) ⟫ʷ
wp0594 c4 = pw1 c4 (CCZ034 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0595 : Complete 4 → ⟪ (Sw23 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw23 ∷ []) ⟫ʷ
wp0595 c4 = pw1 c4 (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) tt tt Eq.refl

wp0596 : Complete 4 → ⟪ (CCZ024 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ034 ∷ []) ⟫ʷ
wp0596 c4 = pw1 c4 (CCZ024 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0597 : Complete 4 → ⟪ (Sw23 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw23 ∷ []) ⟫ʷ
wp0597 c4 = pw1 c4 (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) tt tt Eq.refl

wp0598 : Complete 4 → ⟪ (CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0598 c4 = pw1 c4 (CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0599 : Complete 4 → ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ ι ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0599 c4 = pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0600 : Complete 4 → ⟪ (Toff213 ∷ ι1 ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) ⟫ʷ
wp0600 c4 = pw0 c4 (Toff213 ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) tt tt Eq.refl

wp0601 : Complete 4 → ⟪ (CCZ024 ∷ ι ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0601 c4 = pw1 c4 (CCZ024 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0602 : Complete 4 → ⟪ (S0 ∷ CS04⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ []) ⟫ʷ
wp0602 c4 = pw1 c4 (S0 ∷ CS04⁻ ∷ X4 ∷ []) (X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0603 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0603 c4 = pw1 c4 (CS04 ∷ X4 ∷ []) (X4 ∷ S0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0604 : Complete 4 → ⟪ (S1 ∷ CS14⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S1 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0604 c4 = pw2 c4 (S1 ∷ CS14⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0605 : Complete 4 → ⟪ (CCZ024 ∷ S1 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0605 c4 = pw3 c4 (CCZ024 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0606 : Complete 4 → ⟪ (CS03⁻ ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS24⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
wp0606 c4 = pw1 c4 (CS03⁻ ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0607 : Complete 4 → ⟪ (CS03 ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS24⁻ ∷ CS03 ∷ []) ⟫ʷ
wp0607 c4 = pw1 c4 (CS03 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CS03 ∷ []) tt tt Eq.refl

wp0608 : Complete 4 → ⟪ (S3 ∷ CS34⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0608 c4 = pw2 c4 (S3 ∷ CS34⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0609 : Complete 4 → ⟪ (CCZ024 ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0609 c4 = pw1 c4 (CCZ024 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0610 : Complete 4 → ⟪ (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ []) ⟫ʷ
wp0610 c4 = pw1 c4 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0611 : Complete 4 → ⟪ (K0 ∷ CK40 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ
wp0611 c4 = pw2 c4 (K0 ∷ CK40 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) tt tt Eq.refl

wp0612 : Complete 4 → ⟪ (CCZ024 ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0612 c4 = pw1 c4 (CCZ024 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0613 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ
wp0613 c4 = pw1 c4 (CK40 ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ []) tt tt Eq.refl

wp0614 : Complete 4 → ⟪ (K1 ∷ CK41 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
wp0614 c4 = pw2 c4 (K1 ∷ CK41 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) tt tt Eq.refl

wp0615 : Complete 4 → ⟪ (CS03⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CK42 ∷ S4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0615 c4 = pw1 c4 (CS03⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0616 : Complete 4 → ⟪ (CS03 ∷ K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CK42 ∷ S4 ∷ CS03 ∷ []) ⟫ʷ
wp0616 c4 = pw1 c4 (CS03 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0617 : Complete 4 → ⟪ (CCZ024 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0617 c4 = pw1 c4 (CCZ024 ∷ S4 ∷ []) (S4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0618 : Complete 4 → ⟪ (K3 ∷ CK43 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
wp0618 c4 = pw2 c4 (K3 ∷ CK43 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) tt tt Eq.refl

wp0619 : Complete 4 → ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ ι1 ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wp0619 c4 = pw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0620 : Complete 4 → ⟪ (Toff023 ∷ ι ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ Toff023 ∷ []) ⟫ʷ
wp0620 c4 = pw1 c4 (Toff023 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff023 ∷ []) tt tt Eq.refl

wp0621 : Complete 4 → ⟪ (CCZ014 ∷ ι ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0621 c4 = pw2 c4 (CCZ014 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0622 : Complete 4 → ⟪ (CS13⁻ ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS04⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wp0622 c4 = pw2 c4 (CS13⁻ ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0623 : Complete 4 → ⟪ (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0623 c4 = pw1 c4 (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) (Toff324 ∷ S0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0624 : Complete 4 → ⟪ (CS13 ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS04⁻ ∷ CS13 ∷ []) ⟫ʷ
wp0624 c4 = pw2 c4 (CS13 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS13 ∷ []) tt tt Eq.refl

wp0625 : Complete 4 → ⟪ (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ
wp0625 c4 = pw1 c4 (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ S2 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp0626 : Complete 4 → ⟪ (CCZ014 ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0626 c4 = pw3 c4 (CCZ014 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0627 : Complete 4 → ⟪ (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0627 c4 = pw1 c4 (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) (Toff023 ∷ S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0628 : Complete 4 → ⟪ (CCZ014 ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS34⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0628 c4 = pw2 c4 (CCZ014 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0629 : Complete 4 → ⟪ (CS13⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CK40 ∷ S4 ∷ CS13⁻ ∷ []) ⟫ʷ
wp0629 c4 = pw2 c4 (CS13⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0630 : Complete 4 → ⟪ (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ
wp0630 c4 = pw1 c4 (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) (Toff324 ∷ K0 ∷ CK40 ∷ S4 ∷ []) tt tt Eq.refl

wp0631 : Complete 4 → ⟪ (CS13 ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CK40 ∷ S4 ∷ CS13 ∷ []) ⟫ʷ
wp0631 c4 = pw2 c4 (CS13 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS13 ∷ []) tt tt Eq.refl

wp0632 : Complete 4 → ⟪ (S4 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ S4 ∷ []) ⟫ʷ
wp0632 c4 = pw1 c4 (S4 ∷ Toff023 ∷ []) (Toff023 ∷ S4 ∷ []) tt tt Eq.refl

wp0633 : Complete 4 → ⟪ (CCZ014 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0633 c4 = pw2 c4 (CCZ014 ∷ S4 ∷ []) (S4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0634 : Complete 4 → ⟪ (CCZ014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0634 c4 = pw2 c4 (CCZ014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0635 : Complete 4 → ⟪ (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
wp0635 c4 = pw1 c4 (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) (Toff024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) tt tt Eq.refl

wp0636 : Complete 4 → ⟪ (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ K3 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
wp0636 c4 = pw1 c4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (Toff034 ∷ K3 ∷ CK43 ∷ S4 ∷ []) tt tt Eq.refl

wp0637 : Complete 4 → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ ι1 ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0637 c4 = pw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0638 : Complete 4 → ⟪ (Toff013 ∷ ι ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ Toff013 ∷ []) ⟫ʷ
wp0638 c4 = pw2 c4 (Toff013 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff013 ∷ []) tt tt Eq.refl

wp0639 : Complete 4 → ⟪ (CS12⁻ ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS04⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wp0639 c4 = pw3 c4 (CS12⁻ ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0640 : Complete 4 → ⟪ (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0640 c4 = pw2 c4 (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) (Toff134 ∷ S0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0641 : Complete 4 → ⟪ (CS12 ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS04⁻ ∷ CS12 ∷ []) ⟫ʷ
wp0641 c4 = pw3 c4 (CS12 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS12 ∷ []) tt tt Eq.refl

wp0642 : Complete 4 → ⟪ (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ S1 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0642 c4 = pw2 c4 (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) (Toff013 ∷ S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0643 : Complete 4 → ⟪ (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0643 c4 = pw2 c4 (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0644 : Complete 4 → ⟪ (CS12⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CK40 ∷ S4 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0644 c4 = pw3 c4 (CS12⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0645 : Complete 4 → ⟪ (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ
wp0645 c4 = pw2 c4 (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) (Toff134 ∷ K0 ∷ CK40 ∷ S4 ∷ []) tt tt Eq.refl

wp0646 : Complete 4 → ⟪ (CS12 ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CK40 ∷ S4 ∷ CS12 ∷ []) ⟫ʷ
wp0646 c4 = pw3 c4 (CS12 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS12 ∷ []) tt tt Eq.refl

wp0647 : Complete 4 → ⟪ (S4 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ S4 ∷ []) ⟫ʷ
wp0647 c4 = pw2 c4 (S4 ∷ Toff013 ∷ []) (Toff013 ∷ S4 ∷ []) tt tt Eq.refl

wp0648 : Complete 4 → ⟪ (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
wp0648 c4 = pw2 c4 (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) (Toff014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) tt tt Eq.refl

wp0649 : Complete 4 → ⟪ (CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CK42 ∷ S4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0649 c4 = pw1 c4 (CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0650 : Complete 4 → ⟪ (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ []) ⟫ʷ
wp0650 c4 = pw2 c4 (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0651 : Complete 4 → ⟪ (CCZ014 ∷ Toff314 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) ⟫ʷ
wp0651 c4 = pw2 c4 (CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0652 : Complete 4 → ⟪ (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ []) ⟫ʷ
wp0652 c4 = pw2 c4 (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0653 : Complete 4 → ⟪ (CCZ024 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ
wp0653 c4 = pw3 c4 (CCZ024 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0654 : Complete 4 → ⟪ (CCZ024 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ
wp0654 c4 = pw3 c4 (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0655 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ014 ∷ CX12 ∷ []) ⟫ʷ
wp0655 c4 = pw3 c4 (CCZ014 ∷ []) (CX12 ∷ CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl

wp0656 : Complete 4 → ⟪ (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ Toff314 ∷ []) ⟫ʷ
wp0656 c4 = pw2 c4 (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0657 : Complete 4 → ⟪ (CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ []) ⟫ʷ
wp0657 c4 = pw1 c4 (CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0658 : Complete 4 → ⟪ (CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ []) ⟫ʷ
wp0658 c4 = pw2 c4 (CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ []) tt tt Eq.refl

wp0659 : Complete 4 → ⟪ (CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0659 c4 = pw1 c4 (CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0660 : Complete 4 → ⟪ (CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
wp0660 c4 = pw2 c4 (CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0661 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) ⟫ʷ
wp0661 c4 = pw1 c4 (CCZ023 ∷ []) (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) tt tt Eq.refl

wp0662 : Complete 4 → ⟪ (CX10 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX10 ∷ []) ⟫ʷ
wp0662 c4 = pw2 c4 (CX10 ∷ Toff314 ∷ []) (Toff314 ∷ CX10 ∷ []) tt tt Eq.refl

wp0663 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ124 ∷ CX10 ∷ []) ⟫ʷ
wp0663 c4 = pw3 c4 (CCZ124 ∷ []) (CX10 ∷ CCZ124 ∷ CX10 ∷ []) tt tt Eq.refl

wp0664 : Complete 4 → ⟪ (CX01 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX01 ∷ Toff304 ∷ []) ⟫ʷ
wp0664 c4 = pw2 c4 (CX01 ∷ Toff314 ∷ []) (Toff314 ∷ CX01 ∷ Toff304 ∷ []) tt tt Eq.refl

wp0665 : Complete 4 → ⟪ (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ023 ∷ []) ⟫ʷ
wp0665 c4 = pw1 c4 (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (Toff304 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0666 : Complete 4 → ⟪ (CX40 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX40 ∷ []) ⟫ʷ
wp0666 c4 = pw2 c4 (CX40 ∷ Toff314 ∷ []) (Toff314 ∷ CX40 ∷ []) tt tt Eq.refl

wp0667 : Complete 4 → ⟪ (Toff304 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff304 ∷ []) ⟫ʷ
wp0667 c4 = pw2 c4 (Toff304 ∷ Toff314 ∷ []) (Toff314 ∷ Toff304 ∷ []) tt tt Eq.refl

wp0668 : Complete 4 → ⟪ (CX01 ∷ Toff304 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
wp0668 c4 = pw2 c4 (CX01 ∷ Toff304 ∷ Toff304 ∷ []) (CX01 ∷ []) tt tt Eq.refl

wp0669 : Complete 4 → ⟪ (CCZ023 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ023 ∷ []) ⟫ʷ
wp0669 c4 = pw1 c4 (CCZ023 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0670 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ024 ∷ CX01 ∷ []) ⟫ʷ
wp0670 c4 = pw3 c4 (CCZ024 ∷ []) (CX01 ∷ CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl

wp0671 : Complete 4 → ⟪ (CCZ124 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0671 c4 = pw3 c4 (CCZ124 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0672 : Complete 4 → ⟪ (CCZ124 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ124 ∷ []) ⟫ʷ
wp0672 c4 = pw3 c4 (CCZ124 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0673 : Complete 4 → ⟪ (CCZ024 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) ⟫ʷ
wp0673 c4 = pw3 c4 (CCZ024 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0674 : Complete 4 → ⟪ (CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wp0674 c4 = pw3 c4 (CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

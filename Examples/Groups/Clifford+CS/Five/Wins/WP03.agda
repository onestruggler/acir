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

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp0474 : Base 4 → WsL → ⟪ (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0474 c4 L = pw1 c4 L (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0475 : Base 4 → WsL → ⟪ (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wp0475 c4 L = pw2 c4 L (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wp0476 : Base 4 → WsL → ⟪ (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wp0476 c4 L = pw1 c4 L (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wp0477 : Base 4 → WsL → ⟪ (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wp0477 c4 L = pw1 c4 L (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wp0478 : Base 4 → WsL → ⟪ (CCZ024 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0478 c4 L = pw1 c4 L (CCZ024 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0479 : Base 4 → WsL → ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0479 c4 L = pw2 c4 L (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0480 : Base 4 → WsL → ⟪ (CS04 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ014 ∷ []) ⟫ʷ
wp0480 c4 L = pw2 c4 L (CS04 ∷ Toff014 ∷ []) (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0481 : Base 4 → WsL → ⟪ (CS04 ∷ CS14 ∷ CCZ014 ∷ CS14 ∷ CZ14 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
wp0481 c4 L = pw2 c4 L (CS04 ∷ CS14 ∷ CCZ014 ∷ CS14 ∷ CZ14 ∷ CCZ014 ∷ []) (CS04 ∷ []) tt tt Eq.refl

wp0482 : Base 4 → WsL → ⟪ (CCZ014 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Toff014 ∷ []) ⟫ʷ
wp0482 c4 L = pw2 c4 L (CCZ014 ∷ K0 ∷ []) (K0 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0483 : Base 4 → WsL → ⟪ (CCZ014 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff014 ∷ []) ⟫ʷ
wp0483 c4 L = pw2 c4 L (CCZ014 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff014 ∷ []) tt tt Eq.refl

wp0484 : Base 4 → WsL → ⟪ (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) ⟫ʷ
wp0484 c4 L = pw1 c4 L (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wp0485 : Base 4 → WsL → ⟪ (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS13 ∷ []) ⟫ʷ
wp0485 c4 L = pw2 c4 L (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS13 ∷ []) tt tt Eq.refl

wp0486 : Base 4 → WsL → ⟪ (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS13⁻ ∷ []) ⟫ʷ
wp0486 c4 L = pw2 c4 L (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0487 : Base 4 → WsL → ⟪ (CS04 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ024 ∷ []) ⟫ʷ
wp0487 c4 L = pw1 c4 L (CS04 ∷ Toff024 ∷ []) (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0488 : Base 4 → WsL → ⟪ (CS04 ∷ CS24 ∷ CCZ024 ∷ CS24 ∷ CZ24 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
wp0488 c4 L = pw1 c4 L (CS04 ∷ CS24 ∷ CCZ024 ∷ CS24 ∷ CZ24 ∷ CCZ024 ∷ []) (CS04 ∷ []) tt tt Eq.refl

wp0489 : Base 4 → WsL → ⟪ (CCZ024 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Toff024 ∷ []) ⟫ʷ
wp0489 c4 L = pw1 c4 L (CCZ024 ∷ K0 ∷ []) (K0 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0490 : Base 4 → WsL → ⟪ (CCZ024 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff024 ∷ []) ⟫ʷ
wp0490 c4 L = pw1 c4 L (CCZ024 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff024 ∷ []) tt tt Eq.refl

wp0491 : Base 4 → WsL → ⟪ (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ []) ⟫ʷ
wp0491 c4 L = pw2 c4 L (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ []) tt tt Eq.refl

wp0492 : Base 4 → WsL → ⟪ (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS12 ∷ []) ⟫ʷ
wp0492 c4 L = pw3 c4 L (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS12 ∷ []) tt tt Eq.refl

wp0493 : Base 4 → WsL → ⟪ (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0493 c4 L = pw3 c4 L (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0494 : Base 4 → WsL → ⟪ (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0494 c4 L = pw2 c4 L (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0495 : Base 4 → WsL → ⟪ (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0495 c4 L = pw2 c4 L (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0496 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) ⟫ʷ
wp0496 c4 L = pw3 c4 L (CCZ024 ∷ []) (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) tt tt Eq.refl

wp0497 : Base 4 → WsL → ⟪ (CX01 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX01 ∷ []) ⟫ʷ
wp0497 c4 L = pw3 c4 L (CX01 ∷ Toff204 ∷ []) (Toff204 ∷ CX01 ∷ []) tt tt Eq.refl

wp0498 : Base 4 → WsL → ⟪ (CCZ023 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ023 ∷ CCZ034 ∷ []) ⟫ʷ
wp0498 c4 L = pw1 c4 L (CCZ023 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ023 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0499 : Base 4 → WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ034 ∷ CX01 ∷ []) ⟫ʷ
wp0499 c4 L = pw2 c4 L (CCZ034 ∷ []) (CX01 ∷ CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl

wp0500 : Base 4 → WsL → ⟪ (CX10 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX10 ∷ Toff214 ∷ []) ⟫ʷ
wp0500 c4 L = pw3 c4 L (CX10 ∷ Toff204 ∷ []) (Toff204 ∷ CX10 ∷ Toff214 ∷ []) tt tt Eq.refl

wp0501 : Base 4 → WsL → ⟪ (CS34 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS34 ∷ []) ⟫ʷ
wp0501 c4 L = pw1 c4 L (CS34 ∷ Toff204 ∷ []) (Toff204 ∷ CS34 ∷ []) tt tt Eq.refl

wp0502 : Base 4 → WsL → ⟪ (CX41 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX41 ∷ []) ⟫ʷ
wp0502 c4 L = pw3 c4 L (CX41 ∷ Toff204 ∷ []) (Toff204 ∷ CX41 ∷ []) tt tt Eq.refl

wp0503 : Base 4 → WsL → ⟪ (Toff204 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff204 ∷ []) ⟫ʷ
wp0503 c4 L = pw3 c4 L (Toff204 ∷ Toff214 ∷ []) (Toff214 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0504 : Base 4 → WsL → ⟪ (CX10 ∷ Toff214 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wp0504 c4 L = pw3 c4 L (CX10 ∷ Toff214 ∷ Toff214 ∷ []) (CX10 ∷ []) tt tt Eq.refl

wp0505 : Base 4 → WsL → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ134 ∷ CX10 ∷ []) ⟫ʷ
wp0505 c4 L = pw2 c4 L (CCZ134 ∷ []) (CX10 ∷ CCZ134 ∷ CX10 ∷ []) tt tt Eq.refl

wp0506 : Base 4 → WsL → ⟪ (CCZ034 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) ⟫ʷ
wp0506 c4 L = pw2 c4 L (CCZ034 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0507 : Base 4 → WsL → ⟪ (CCZ134 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ
wp0507 c4 L = pw2 c4 L (CCZ134 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0508 : Base 4 → WsL → ⟪ (CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0508 c4 L = pw2 c4 L (CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0509 : Base 4 → WsL → ⟪ (CCZ124 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ024 ∷ []) ⟫ʷ
wp0509 c4 L = pw3 c4 L (CCZ124 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0510 : Base 4 → WsL → ⟪ (Sw01 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw01 ∷ []) ⟫ʷ
wp0510 c4 L = pw3 c4 L (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0511 : Base 4 → WsL → ⟪ (CCZ024 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ124 ∷ []) ⟫ʷ
wp0511 c4 L = pw3 c4 L (CCZ024 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0512 : Base 4 → WsL → ⟪ (Sw01 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw01 ∷ []) ⟫ʷ
wp0512 c4 L = pw3 c4 L (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0513 : Base 4 → WsL → ⟪ (CCZ023 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ023 ∷ []) ⟫ʷ
wp0513 c4 L = pw1 c4 L (CCZ023 ∷ CS24 ∷ []) (CS24 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0514 : Base 4 → WsL → ⟪ (CS03⁻ ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
wp0514 c4 L = pw2 c4 L (CS03⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0515 : Base 4 → WsL → ⟪ (CCZ124 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ124 ∷ []) ⟫ʷ
wp0515 c4 L = pw3 c4 L (CCZ124 ∷ CS02 ∷ []) (CS02 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0516 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wp0516 c4 L = pw3 c4 L (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wp0517 : Base 4 → WsL → ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0517 c4 L = pw2 c4 L (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0518 : Base 4 → WsL → ⟪ (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0518 c4 L = pw2 c4 L (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0519 : Base 4 → WsL → ⟪ (CX43 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX43 ∷ []) ⟫ʷ
wp0519 c4 L = pw1 c4 L (CX43 ∷ Toff024 ∷ []) (Toff024 ∷ CX43 ∷ []) tt tt Eq.refl

wp0520 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ014 ∷ CCZ124 ∷ []) ⟫ʷ
wp0520 c4 L = pw3 c4 L (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0521 : Base 4 → WsL → ⟪ (CCZ013 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wp0521 c4 L = pw2 c4 L (CCZ013 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0522 : Base 4 → WsL → ⟪ (CX34 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX34 ∷ Toff023 ∷ []) ⟫ʷ
wp0522 c4 L = pw1 c4 L (CX34 ∷ Toff024 ∷ []) (Toff024 ∷ CX34 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0523 : Base 4 → WsL → ⟪ (CCZ013 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ013 ∷ []) ⟫ʷ
wp0523 c4 L = pw2 c4 L (CCZ013 ∷ CX34 ∷ []) (CX34 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0524 : Base 4 → WsL → ⟪ (CS12 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS12 ∷ []) ⟫ʷ
wp0524 c4 L = pw3 c4 L (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) tt tt Eq.refl

wp0525 : Base 4 → WsL → ⟪ (CX23 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX23 ∷ []) ⟫ʷ
wp0525 c4 L = pw1 c4 L (CX23 ∷ Toff024 ∷ []) (Toff024 ∷ CX23 ∷ []) tt tt Eq.refl

wp0526 : Base 4 → WsL → ⟪ (CX34 ∷ Toff023 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ []) ⟫ʷ
wp0526 c4 L = pw1 c4 L (CX34 ∷ Toff023 ∷ Toff023 ∷ []) (CX34 ∷ []) tt tt Eq.refl

wp0527 : Base 4 → WsL → ⟪ (CCZ023 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ024 ∷ []) ⟫ʷ
wp0527 c4 L = pw1 c4 L (CCZ023 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0528 : Base 4 → WsL → ⟪ (Sw34 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw34 ∷ []) ⟫ʷ
wp0528 c4 L = pw1 c4 L (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0529 : Base 4 → WsL → ⟪ (CCZ024 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ023 ∷ []) ⟫ʷ
wp0529 c4 L = pw1 c4 L (CCZ024 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0530 : Base 4 → WsL → ⟪ (Sw34 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw34 ∷ []) ⟫ʷ
wp0530 c4 L = pw1 c4 L (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0531 : Base 4 → WsL → ⟪ (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) ⟫ʷ
wp0531 c4 L = pw2 c4 L (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0532 : Base 4 → WsL → ⟪ (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0532 c4 L = pw1 c4 L (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0533 : Base 4 → WsL → ⟪ (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0533 c4 L = pw1 c4 L (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0534 : Base 4 → WsL → ⟪ (CS24 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) ⟫ʷ
wp0534 c4 L = pw1 c4 L (CS24 ∷ Toff204 ∷ []) (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0535 : Base 4 → WsL → ⟪ (CS24 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ []) ⟫ʷ
wp0535 c4 L = pw1 c4 L (CS24 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) (CS24 ∷ []) tt tt Eq.refl

wp0536 : Base 4 → WsL → ⟪ (CCZ024 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Toff204 ∷ []) ⟫ʷ
wp0536 c4 L = pw1 c4 L (CCZ024 ∷ K2 ∷ []) (K2 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0537 : Base 4 → WsL → ⟪ (CCZ024 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Toff204 ∷ []) ⟫ʷ
wp0537 c4 L = pw1 c4 L (CCZ024 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff204 ∷ []) tt tt Eq.refl

wp0538 : Base 4 → WsL → ⟪ (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS03 ∷ []) ⟫ʷ
wp0538 c4 L = pw1 c4 L (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0539 : Base 4 → WsL → ⟪ (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0539 c4 L = pw1 c4 L (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0540 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) ⟫ʷ
wp0540 c4 L = pw2 c4 L (CCZ014 ∷ []) (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) tt tt Eq.refl

wp0541 : Base 4 → WsL → ⟪ (CX12 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX12 ∷ []) ⟫ʷ
wp0541 c4 L = pw3 c4 L (CX12 ∷ Toff014 ∷ []) (Toff014 ∷ CX12 ∷ []) tt tt Eq.refl

wp0542 : Base 4 → WsL → ⟪ (CCZ013 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ013 ∷ CCZ134 ∷ []) ⟫ʷ
wp0542 c4 L = pw2 c4 L (CCZ013 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ013 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0543 : Base 4 → WsL → ⟪ (CCZ023 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ023 ∷ []) ⟫ʷ
wp0543 c4 L = pw1 c4 L (CCZ023 ∷ CS34 ∷ []) (CS34 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0544 : Base 4 → WsL → ⟪ (CX21 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX21 ∷ Toff024 ∷ []) ⟫ʷ
wp0544 c4 L = pw3 c4 L (CX21 ∷ Toff014 ∷ []) (Toff014 ∷ CX21 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0545 : Base 4 → WsL → ⟪ (CCZ023 ∷ Toff024 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ023 ∷ []) ⟫ʷ
wp0545 c4 L = pw1 c4 L (CCZ023 ∷ Toff024 ∷ CCZ234 ∷ []) (Toff024 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0546 : Base 4 → WsL → ⟪ (CS34 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS34 ∷ []) ⟫ʷ
wp0546 c4 L = pw2 c4 L (CS34 ∷ Toff014 ∷ []) (Toff014 ∷ CS34 ∷ []) tt tt Eq.refl

wp0547 : Base 4 → WsL → ⟪ (CX42 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX42 ∷ []) ⟫ʷ
wp0547 c4 L = pw3 c4 L (CX42 ∷ Toff014 ∷ []) (Toff014 ∷ CX42 ∷ []) tt tt Eq.refl

wp0548 : Base 4 → WsL → ⟪ (Toff014 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff014 ∷ []) ⟫ʷ
wp0548 c4 L = pw3 c4 L (Toff014 ∷ Toff024 ∷ []) (Toff024 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0549 : Base 4 → WsL → ⟪ (CX21 ∷ Toff024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wp0549 c4 L = pw3 c4 L (CX21 ∷ Toff024 ∷ Toff024 ∷ []) (CX21 ∷ []) tt tt Eq.refl

wp0550 : Base 4 → WsL → ⟪ (CCZ023 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ023 ∷ []) ⟫ʷ
wp0550 c4 L = pw1 c4 L (CCZ023 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0551 : Base 4 → WsL → ⟪ (CCZ024 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ014 ∷ []) ⟫ʷ
wp0551 c4 L = pw3 c4 L (CCZ024 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0552 : Base 4 → WsL → ⟪ (Sw12 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw12 ∷ []) ⟫ʷ
wp0552 c4 L = pw3 c4 L (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) tt tt Eq.refl

wp0553 : Base 4 → WsL → ⟪ (CCZ014 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ024 ∷ []) ⟫ʷ
wp0553 c4 L = pw3 c4 L (CCZ014 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0554 : Base 4 → WsL → ⟪ (Sw12 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw12 ∷ []) ⟫ʷ
wp0554 c4 L = pw3 c4 L (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) tt tt Eq.refl

wp0555 : Base 4 → WsL → ⟪ (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ []) ⟫ʷ
wp0555 c4 L = pw1 c4 L (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0556 : Base 4 → WsL → ⟪ (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0556 c4 L = pw1 c4 L (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0557 : Base 4 → WsL → ⟪ (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0557 c4 L = pw1 c4 L (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0558 : Base 4 → WsL → ⟪ (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0558 c4 L = pw1 c4 L (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0559 : Base 4 → WsL → ⟪ (CCZ234 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) ⟫ʷ
wp0559 c4 L = pw1 c4 L (CCZ234 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0560 : Base 4 → WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ034 ∷ CX41 ∷ []) ⟫ʷ
wp0560 c4 L = pw2 c4 L (CCZ034 ∷ []) (CX41 ∷ CCZ034 ∷ CX41 ∷ []) tt tt Eq.refl

wp0561 : Base 4 → WsL → ⟪ (CX14 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX14 ∷ Toff201 ∷ []) ⟫ʷ
wp0561 c4 L = pw3 c4 L (CX14 ∷ Toff204 ∷ []) (Toff204 ∷ CX14 ∷ Toff201 ∷ []) tt tt Eq.refl

wp0562 : Base 4 → WsL → ⟪ (CS03 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS03 ∷ []) ⟫ʷ
wp0562 c4 L = pw1 c4 L (CS03 ∷ Toff204 ∷ []) (Toff204 ∷ CS03 ∷ []) tt tt Eq.refl

wp0563 : Base 4 → WsL → ⟪ (Toff201 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff201 ∷ []) ⟫ʷ
wp0563 c4 L = pw3 c4 L (Toff201 ∷ Toff204 ∷ []) (Toff204 ∷ Toff201 ∷ []) tt tt Eq.refl

wp0564 : Base 4 → WsL → ⟪ (CX14 ∷ Toff201 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wp0564 c4 L = pw3 c4 L (CX14 ∷ Toff201 ∷ Toff201 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wp0565 : Base 4 → WsL → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ013 ∷ CX14 ∷ []) ⟫ʷ
wp0565 c4 L = pw2 c4 L (CCZ013 ∷ []) (CX14 ∷ CCZ013 ∷ CX14 ∷ []) tt tt Eq.refl

wp0566 : Base 4 → WsL → ⟪ (CCZ034 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) ⟫ʷ
wp0566 c4 L = pw2 c4 L (CCZ034 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0567 : Base 4 → WsL → ⟪ (CCZ013 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) ⟫ʷ
wp0567 c4 L = pw2 c4 L (CCZ013 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0568 : Base 4 → WsL → ⟪ (CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0568 c4 L = pw2 c4 L (CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0569 : Base 4 → WsL → ⟪ (Sw14 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Sw14 ∷ []) ⟫ʷ
wp0569 c4 L = pw3 c4 L (Sw14 ∷ Toff204 ∷ []) (Toff201 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0570 : Base 4 → WsL → ⟪ (Sw14 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw14 ∷ []) ⟫ʷ
wp0570 c4 L = pw3 c4 L (Sw14 ∷ Toff012 ∷ []) (Toff024 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0571 : Base 4 → WsL → ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0571 c4 L = pw2 c4 L (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0572 : Base 4 → WsL → ⟪ (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CCZ023 ∷ []) ⟫ʷ
wp0572 c4 L = pw1 c4 L (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) (CX42 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0573 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ
wp0573 c4 L = pw2 c4 L (CCZ034 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0574 : Base 4 → WsL → ⟪ (CCZ023 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wp0574 c4 L = pw1 c4 L (CCZ023 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0575 : Base 4 → WsL → ⟪ (CCZ023 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ023 ∷ []) ⟫ʷ
wp0575 c4 L = pw1 c4 L (CCZ023 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0576 : Base 4 → WsL → ⟪ (CX42 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ []) ⟫ʷ
wp0576 c4 L = pw1 c4 L (CX42 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX42 ∷ []) tt tt Eq.refl

wp0577 : Base 4 → WsL → ⟪ (CX24 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX24 ∷ Toff012 ∷ []) ⟫ʷ
wp0577 c4 L = pw3 c4 L (CX24 ∷ Toff014 ∷ []) (Toff014 ∷ CX24 ∷ Toff012 ∷ []) tt tt Eq.refl

wp0578 : Base 4 → WsL → ⟪ (CCZ023 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ CCZ023 ∷ []) ⟫ʷ
wp0578 c4 L = pw1 c4 L (CCZ023 ∷ CX24 ∷ []) (CX24 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0579 : Base 4 → WsL → ⟪ (CS13 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS13 ∷ []) ⟫ʷ
wp0579 c4 L = pw2 c4 L (CS13 ∷ Toff014 ∷ []) (Toff014 ∷ CS13 ∷ []) tt tt Eq.refl

wp0580 : Base 4 → WsL → ⟪ (Toff012 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff012 ∷ []) ⟫ʷ
wp0580 c4 L = pw3 c4 L (Toff012 ∷ Toff014 ∷ []) (Toff014 ∷ Toff012 ∷ []) tt tt Eq.refl

wp0581 : Base 4 → WsL → ⟪ (CX24 ∷ Toff012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ []) ⟫ʷ
wp0581 c4 L = pw3 c4 L (CX24 ∷ Toff012 ∷ Toff012 ∷ []) (CX24 ∷ []) tt tt Eq.refl

wp0582 : Base 4 → WsL → ⟪ (CCZ012 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ CCZ014 ∷ []) ⟫ʷ
wp0582 c4 L = pw3 c4 L (CCZ012 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0583 : Base 4 → WsL → ⟪ (Sw24 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sw24 ∷ []) ⟫ʷ
wp0583 c4 L = pw3 c4 L (Sw24 ∷ Toff014 ∷ []) (Toff012 ∷ Sw24 ∷ []) tt tt Eq.refl

wp0584 : Base 4 → WsL → ⟪ (CCZ014 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ CCZ012 ∷ []) ⟫ʷ
wp0584 c4 L = pw3 c4 L (CCZ014 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0585 : Base 4 → WsL → ⟪ (Sw24 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw24 ∷ []) ⟫ʷ
wp0585 c4 L = pw3 c4 L (Sw24 ∷ Toff102 ∷ []) (Toff104 ∷ Sw24 ∷ []) tt tt Eq.refl

wp0586 : Base 4 → WsL → ⟪ (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ []) ⟫ʷ
wp0586 c4 L = pw1 c4 L (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0587 : Base 4 → WsL → ⟪ (CCZ012 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) ⟫ʷ
wp0587 c4 L = pw3 c4 L (CCZ012 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0588 : Base 4 → WsL → ⟪ (CX32 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX32 ∷ Toff034 ∷ []) ⟫ʷ
wp0588 c4 L = pw1 c4 L (CX32 ∷ Toff024 ∷ []) (Toff024 ∷ CX32 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0589 : Base 4 → WsL → ⟪ (CCZ013 ∷ Toff034 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ013 ∷ []) ⟫ʷ
wp0589 c4 L = pw2 c4 L (CCZ013 ∷ Toff034 ∷ CCZ134 ∷ []) (Toff034 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0590 : Base 4 → WsL → ⟪ (CS14 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS14 ∷ []) ⟫ʷ
wp0590 c4 L = pw3 c4 L (CS14 ∷ Toff024 ∷ []) (Toff024 ∷ CS14 ∷ []) tt tt Eq.refl

wp0591 : Base 4 → WsL → ⟪ (Toff024 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff024 ∷ []) ⟫ʷ
wp0591 c4 L = pw1 c4 L (Toff024 ∷ Toff034 ∷ []) (Toff034 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0592 : Base 4 → WsL → ⟪ (CX32 ∷ Toff034 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
wp0592 c4 L = pw1 c4 L (CX32 ∷ Toff034 ∷ Toff034 ∷ []) (CX32 ∷ []) tt tt Eq.refl

wp0593 : Base 4 → WsL → ⟪ (CCZ013 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ013 ∷ []) ⟫ʷ
wp0593 c4 L = pw2 c4 L (CCZ013 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0594 : Base 4 → WsL → ⟪ (CCZ034 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ024 ∷ []) ⟫ʷ
wp0594 c4 L = pw1 c4 L (CCZ034 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0595 : Base 4 → WsL → ⟪ (Sw23 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw23 ∷ []) ⟫ʷ
wp0595 c4 L = pw1 c4 L (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) tt tt Eq.refl

wp0596 : Base 4 → WsL → ⟪ (CCZ024 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ034 ∷ []) ⟫ʷ
wp0596 c4 L = pw1 c4 L (CCZ024 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0597 : Base 4 → WsL → ⟪ (Sw23 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw23 ∷ []) ⟫ʷ
wp0597 c4 L = pw1 c4 L (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) tt tt Eq.refl

wp0598 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0598 c4 L = pw1 c4 L (CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0599 : Base 4 → WsL → ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ ι ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0599 c4 L = pw2 c4 L (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0600 : Base 4 → WsL → ⟪ (Toff213 ∷ ι1 ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) ⟫ʷ
wp0600 c4 L = pw0 c4 L (Toff213 ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) tt tt Eq.refl

wp0601 : Base 4 → WsL → ⟪ (CCZ024 ∷ ι ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0601 c4 L = pw1 c4 L (CCZ024 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0602 : Base 4 → WsL → ⟪ (S0 ∷ CS04⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ []) ⟫ʷ
wp0602 c4 L = pw1 c4 L (S0 ∷ CS04⁻ ∷ X4 ∷ []) (X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0603 : Base 4 → WsL → ⟪ (CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0603 c4 L = pw1 c4 L (CS04 ∷ X4 ∷ []) (X4 ∷ S0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0604 : Base 4 → WsL → ⟪ (S1 ∷ CS14⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S1 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0604 c4 L = pw2 c4 L (S1 ∷ CS14⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0605 : Base 4 → WsL → ⟪ (CCZ024 ∷ S1 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0605 c4 L = pw3 c4 L (CCZ024 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0606 : Base 4 → WsL → ⟪ (CS03⁻ ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS24⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
wp0606 c4 L = pw1 c4 L (CS03⁻ ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0607 : Base 4 → WsL → ⟪ (CS03 ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS24⁻ ∷ CS03 ∷ []) ⟫ʷ
wp0607 c4 L = pw1 c4 L (CS03 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CS03 ∷ []) tt tt Eq.refl

wp0608 : Base 4 → WsL → ⟪ (S3 ∷ CS34⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0608 c4 L = pw2 c4 L (S3 ∷ CS34⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0609 : Base 4 → WsL → ⟪ (CCZ024 ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0609 c4 L = pw1 c4 L (CCZ024 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0610 : Base 4 → WsL → ⟪ (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ []) ⟫ʷ
wp0610 c4 L = pw1 c4 L (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0611 : Base 4 → WsL → ⟪ (K0 ∷ CK40 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ
wp0611 c4 L = pw2 c4 L (K0 ∷ CK40 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) tt tt Eq.refl

wp0612 : Base 4 → WsL → ⟪ (CCZ024 ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0612 c4 L = pw1 c4 L (CCZ024 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0613 : Base 4 → WsL → ⟪ (CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ
wp0613 c4 L = pw1 c4 L (CK40 ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ []) tt tt Eq.refl

wp0614 : Base 4 → WsL → ⟪ (K1 ∷ CK41 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
wp0614 c4 L = pw2 c4 L (K1 ∷ CK41 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) tt tt Eq.refl

wp0615 : Base 4 → WsL → ⟪ (CS03⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CK42 ∷ S4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0615 c4 L = pw1 c4 L (CS03⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0616 : Base 4 → WsL → ⟪ (CS03 ∷ K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CK42 ∷ S4 ∷ CS03 ∷ []) ⟫ʷ
wp0616 c4 L = pw1 c4 L (CS03 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0617 : Base 4 → WsL → ⟪ (CCZ024 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0617 c4 L = pw1 c4 L (CCZ024 ∷ S4 ∷ []) (S4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0618 : Base 4 → WsL → ⟪ (K3 ∷ CK43 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
wp0618 c4 L = pw2 c4 L (K3 ∷ CK43 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) tt tt Eq.refl

wp0619 : Base 4 → WsL → ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ ι1 ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wp0619 c4 L = pw0 c4 L (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0620 : Base 4 → WsL → ⟪ (Toff023 ∷ ι ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ Toff023 ∷ []) ⟫ʷ
wp0620 c4 L = pw1 c4 L (Toff023 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff023 ∷ []) tt tt Eq.refl

wp0621 : Base 4 → WsL → ⟪ (CCZ014 ∷ ι ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0621 c4 L = pw2 c4 L (CCZ014 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0622 : Base 4 → WsL → ⟪ (CS13⁻ ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS04⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wp0622 c4 L = pw2 c4 L (CS13⁻ ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0623 : Base 4 → WsL → ⟪ (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0623 c4 L = pw1 c4 L (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) (Toff324 ∷ S0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0624 : Base 4 → WsL → ⟪ (CS13 ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS04⁻ ∷ CS13 ∷ []) ⟫ʷ
wp0624 c4 L = pw2 c4 L (CS13 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS13 ∷ []) tt tt Eq.refl

wp0625 : Base 4 → WsL → ⟪ (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ
wp0625 c4 L = pw1 c4 L (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ S2 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp0626 : Base 4 → WsL → ⟪ (CCZ014 ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0626 c4 L = pw3 c4 L (CCZ014 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0627 : Base 4 → WsL → ⟪ (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0627 c4 L = pw1 c4 L (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) (Toff023 ∷ S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0628 : Base 4 → WsL → ⟪ (CCZ014 ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS34⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0628 c4 L = pw2 c4 L (CCZ014 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0629 : Base 4 → WsL → ⟪ (CS13⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CK40 ∷ S4 ∷ CS13⁻ ∷ []) ⟫ʷ
wp0629 c4 L = pw2 c4 L (CS13⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0630 : Base 4 → WsL → ⟪ (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ
wp0630 c4 L = pw1 c4 L (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) (Toff324 ∷ K0 ∷ CK40 ∷ S4 ∷ []) tt tt Eq.refl

wp0631 : Base 4 → WsL → ⟪ (CS13 ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CK40 ∷ S4 ∷ CS13 ∷ []) ⟫ʷ
wp0631 c4 L = pw2 c4 L (CS13 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS13 ∷ []) tt tt Eq.refl

wp0632 : Base 4 → WsL → ⟪ (S4 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ S4 ∷ []) ⟫ʷ
wp0632 c4 L = pw1 c4 L (S4 ∷ Toff023 ∷ []) (Toff023 ∷ S4 ∷ []) tt tt Eq.refl

wp0633 : Base 4 → WsL → ⟪ (CCZ014 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0633 c4 L = pw2 c4 L (CCZ014 ∷ S4 ∷ []) (S4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0634 : Base 4 → WsL → ⟪ (CCZ014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0634 c4 L = pw2 c4 L (CCZ014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0635 : Base 4 → WsL → ⟪ (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
wp0635 c4 L = pw1 c4 L (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) (Toff024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) tt tt Eq.refl

wp0636 : Base 4 → WsL → ⟪ (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ K3 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
wp0636 c4 L = pw1 c4 L (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (Toff034 ∷ K3 ∷ CK43 ∷ S4 ∷ []) tt tt Eq.refl

wp0637 : Base 4 → WsL → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ ι1 ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0637 c4 L = pw0 c4 L (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0638 : Base 4 → WsL → ⟪ (Toff013 ∷ ι ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ Toff013 ∷ []) ⟫ʷ
wp0638 c4 L = pw2 c4 L (Toff013 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff013 ∷ []) tt tt Eq.refl

wp0639 : Base 4 → WsL → ⟪ (CS12⁻ ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS04⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wp0639 c4 L = pw3 c4 L (CS12⁻ ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0640 : Base 4 → WsL → ⟪ (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0640 c4 L = pw2 c4 L (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) (Toff134 ∷ S0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0641 : Base 4 → WsL → ⟪ (CS12 ∷ S0 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS04⁻ ∷ CS12 ∷ []) ⟫ʷ
wp0641 c4 L = pw3 c4 L (CS12 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS12 ∷ []) tt tt Eq.refl

wp0642 : Base 4 → WsL → ⟪ (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ S1 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0642 c4 L = pw2 c4 L (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) (Toff013 ∷ S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0643 : Base 4 → WsL → ⟪ (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0643 c4 L = pw2 c4 L (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0644 : Base 4 → WsL → ⟪ (CS12⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CK40 ∷ S4 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0644 c4 L = pw3 c4 L (CS12⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0645 : Base 4 → WsL → ⟪ (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ
wp0645 c4 L = pw2 c4 L (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) (Toff134 ∷ K0 ∷ CK40 ∷ S4 ∷ []) tt tt Eq.refl

wp0646 : Base 4 → WsL → ⟪ (CS12 ∷ K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CK40 ∷ S4 ∷ CS12 ∷ []) ⟫ʷ
wp0646 c4 L = pw3 c4 L (CS12 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS12 ∷ []) tt tt Eq.refl

wp0647 : Base 4 → WsL → ⟪ (S4 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ S4 ∷ []) ⟫ʷ
wp0647 c4 L = pw2 c4 L (S4 ∷ Toff013 ∷ []) (Toff013 ∷ S4 ∷ []) tt tt Eq.refl

wp0648 : Base 4 → WsL → ⟪ (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
wp0648 c4 L = pw2 c4 L (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) (Toff014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) tt tt Eq.refl

wp0649 : Base 4 → WsL → ⟪ (CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CK42 ∷ S4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0649 c4 L = pw1 c4 L (CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0650 : Base 4 → WsL → ⟪ (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ []) ⟫ʷ
wp0650 c4 L = pw2 c4 L (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0651 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff314 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) ⟫ʷ
wp0651 c4 L = pw2 c4 L (CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0652 : Base 4 → WsL → ⟪ (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ []) ⟫ʷ
wp0652 c4 L = pw2 c4 L (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0653 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ
wp0653 c4 L = pw3 c4 L (CCZ024 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0654 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ
wp0654 c4 L = pw3 c4 L (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0655 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ014 ∷ CX12 ∷ []) ⟫ʷ
wp0655 c4 L = pw3 c4 L (CCZ014 ∷ []) (CX12 ∷ CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl

wp0656 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ Toff314 ∷ []) ⟫ʷ
wp0656 c4 L = pw2 c4 L (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0657 : Base 4 → WsL → ⟪ (CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ []) ⟫ʷ
wp0657 c4 L = pw1 c4 L (CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0658 : Base 4 → WsL → ⟪ (CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ []) ⟫ʷ
wp0658 c4 L = pw2 c4 L (CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ []) tt tt Eq.refl

wp0659 : Base 4 → WsL → ⟪ (CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0659 c4 L = pw1 c4 L (CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0660 : Base 4 → WsL → ⟪ (CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
wp0660 c4 L = pw2 c4 L (CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0661 : Base 4 → WsL → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) ⟫ʷ
wp0661 c4 L = pw1 c4 L (CCZ023 ∷ []) (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) tt tt Eq.refl

wp0662 : Base 4 → WsL → ⟪ (CX10 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX10 ∷ []) ⟫ʷ
wp0662 c4 L = pw2 c4 L (CX10 ∷ Toff314 ∷ []) (Toff314 ∷ CX10 ∷ []) tt tt Eq.refl

wp0663 : Base 4 → WsL → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ124 ∷ CX10 ∷ []) ⟫ʷ
wp0663 c4 L = pw3 c4 L (CCZ124 ∷ []) (CX10 ∷ CCZ124 ∷ CX10 ∷ []) tt tt Eq.refl

wp0664 : Base 4 → WsL → ⟪ (CX01 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX01 ∷ Toff304 ∷ []) ⟫ʷ
wp0664 c4 L = pw2 c4 L (CX01 ∷ Toff314 ∷ []) (Toff314 ∷ CX01 ∷ Toff304 ∷ []) tt tt Eq.refl

wp0665 : Base 4 → WsL → ⟪ (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ023 ∷ []) ⟫ʷ
wp0665 c4 L = pw1 c4 L (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (Toff304 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0666 : Base 4 → WsL → ⟪ (CX40 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX40 ∷ []) ⟫ʷ
wp0666 c4 L = pw2 c4 L (CX40 ∷ Toff314 ∷ []) (Toff314 ∷ CX40 ∷ []) tt tt Eq.refl

wp0667 : Base 4 → WsL → ⟪ (Toff304 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff304 ∷ []) ⟫ʷ
wp0667 c4 L = pw2 c4 L (Toff304 ∷ Toff314 ∷ []) (Toff314 ∷ Toff304 ∷ []) tt tt Eq.refl

wp0668 : Base 4 → WsL → ⟪ (CX01 ∷ Toff304 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
wp0668 c4 L = pw2 c4 L (CX01 ∷ Toff304 ∷ Toff304 ∷ []) (CX01 ∷ []) tt tt Eq.refl

wp0669 : Base 4 → WsL → ⟪ (CCZ023 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ023 ∷ []) ⟫ʷ
wp0669 c4 L = pw1 c4 L (CCZ023 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0670 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ024 ∷ CX01 ∷ []) ⟫ʷ
wp0670 c4 L = pw3 c4 L (CCZ024 ∷ []) (CX01 ∷ CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl

wp0671 : Base 4 → WsL → ⟪ (CCZ124 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0671 c4 L = pw3 c4 L (CCZ124 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0672 : Base 4 → WsL → ⟪ (CCZ124 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ124 ∷ []) ⟫ʷ
wp0672 c4 L = pw3 c4 L (CCZ124 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0673 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) ⟫ʷ
wp0673 c4 L = pw3 c4 L (CCZ024 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0674 : Base 4 → WsL → ⟪ (CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wp0674 c4 L = pw3 c4 L (CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

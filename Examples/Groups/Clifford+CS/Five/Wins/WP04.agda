------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP04 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp0675 : Base 4 → WsL → ⟪ (CCZ034 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ134 ∷ []) ⟫ʷ
wp0675 c4 L = pw2 c4 L (CCZ034 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0676 : Base 4 → WsL → ⟪ (Sw01 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw01 ∷ []) ⟫ʷ
wp0676 c4 L = pw2 c4 L (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0677 : Base 4 → WsL → ⟪ (CCZ134 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ034 ∷ []) ⟫ʷ
wp0677 c4 L = pw2 c4 L (CCZ134 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0678 : Base 4 → WsL → ⟪ (Sw01 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sw01 ∷ []) ⟫ʷ
wp0678 c4 L = pw2 c4 L (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0679 : Base 4 → WsL → ⟪ (CCZ124 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ124 ∷ []) ⟫ʷ
wp0679 c4 L = pw3 c4 L (CCZ124 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0680 : Base 4 → WsL → ⟪ (CCZ023 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ023 ∷ []) ⟫ʷ
wp0680 c4 L = pw1 c4 L (CCZ023 ∷ CX34 ∷ []) (CX34 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0681 : Base 4 → WsL → ⟪ (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ []) ⟫ʷ
wp0681 c4 L = pw1 c4 L (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl

wp0682 : Base 4 → WsL → ⟪ (CS04⁻ ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0682 c4 L = pw3 c4 L (CS04⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0683 : Base 4 → WsL → ⟪ (CS04 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS04 ∷ []) ⟫ʷ
wp0683 c4 L = pw3 c4 L (CS04 ∷ Toff214 ∷ []) (Toff214 ∷ CS04 ∷ []) tt tt Eq.refl

wp0684 : Base 4 → WsL → ⟪ (CCZ023 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ CCZ023 ∷ []) ⟫ʷ
wp0684 c4 L = pw1 c4 L (CCZ023 ∷ CX04 ∷ []) (CX04 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0685 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ
wp0685 c4 L = pw3 c4 L (CCZ014 ∷ []) (CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0686 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ014 ∷ []) ⟫ʷ
wp0686 c4 L = pw3 c4 L (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0687 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ014 ∷ []) ⟫ʷ
wp0687 c4 L = pw2 c4 L (CCZ014 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0688 : Base 4 → WsL → ⟪ (CX01 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX01 ∷ []) ⟫ʷ
wp0688 c4 L = pw2 c4 L (CX01 ∷ Toff304 ∷ []) (Toff304 ∷ CX01 ∷ []) tt tt Eq.refl

wp0689 : Base 4 → WsL → ⟪ (CCZ023 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ023 ∷ CCZ024 ∷ []) ⟫ʷ
wp0689 c4 L = pw1 c4 L (CCZ023 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0690 : Base 4 → WsL → ⟪ (CX10 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX10 ∷ Toff314 ∷ []) ⟫ʷ
wp0690 c4 L = pw2 c4 L (CX10 ∷ Toff304 ∷ []) (Toff304 ∷ CX10 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0691 : Base 4 → WsL → ⟪ (CS24 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS24 ∷ []) ⟫ʷ
wp0691 c4 L = pw1 c4 L (CS24 ∷ Toff304 ∷ []) (Toff304 ∷ CS24 ∷ []) tt tt Eq.refl

wp0692 : Base 4 → WsL → ⟪ (CX41 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX41 ∷ []) ⟫ʷ
wp0692 c4 L = pw2 c4 L (CX41 ∷ Toff304 ∷ []) (Toff304 ∷ CX41 ∷ []) tt tt Eq.refl

wp0693 : Base 4 → WsL → ⟪ (CX10 ∷ Toff314 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wp0693 c4 L = pw2 c4 L (CX10 ∷ Toff314 ∷ Toff314 ∷ []) (CX10 ∷ []) tt tt Eq.refl

wp0694 : Base 4 → WsL → ⟪ (CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp0694 c4 L = pw3 c4 L (CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp0695 : Base 4 → WsL → ⟪ (Sw01 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sw01 ∷ []) ⟫ʷ
wp0695 c4 L = pw2 c4 L (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0696 : Base 4 → WsL → ⟪ (Sw01 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw01 ∷ []) ⟫ʷ
wp0696 c4 L = pw2 c4 L (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0697 : Base 4 → WsL → ⟪ (CZ02 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CZ02 ∷ CCZ014 ∷ []) ⟫ʷ
wp0697 c4 L = pw3 c4 L (CZ02 ∷ Toff214 ∷ []) (Toff214 ∷ CZ02 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0698 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ []) ⟫ʷ
wp0698 c4 L = pw2 c4 L (CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0699 : Base 4 → WsL → ⟪ (CCZ014 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ014 ∷ []) ⟫ʷ
wp0699 c4 L = pw3 c4 L (CCZ014 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0700 : Base 4 → WsL → ⟪ (CCZ034 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0700 c4 L = pw1 c4 L (CCZ034 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0701 : Base 4 → WsL → ⟪ (CCZ034 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CCZ034 ∷ []) ⟫ʷ
wp0701 c4 L = pw1 c4 L (CCZ034 ∷ K2 ∷ []) (K2 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0702 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ034 ∷ []) ⟫ʷ
wp0702 c4 L = pw2 c4 L (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (Toff314 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0703 : Base 4 → WsL → ⟪ (CS02⁻ ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wp0703 c4 L = pw3 c4 L (CS02⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0704 : Base 4 → WsL → ⟪ (CCZ134 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ134 ∷ []) ⟫ʷ
wp0704 c4 L = pw2 c4 L (CCZ134 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0705 : Base 4 → WsL → ⟪ (CCZ134 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ134 ∷ []) ⟫ʷ
wp0705 c4 L = pw2 c4 L (CCZ134 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0706 : Base 4 → WsL → ⟪ (CCZ134 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ134 ∷ []) ⟫ʷ
wp0706 c4 L = pw2 c4 L (CCZ134 ∷ CS03 ∷ []) (CS03 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0707 : Base 4 → WsL → ⟪ (CX10 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX10 ∷ []) ⟫ʷ
wp0707 c4 L = pw3 c4 L (CX10 ∷ Toff214 ∷ []) (Toff214 ∷ CX10 ∷ []) tt tt Eq.refl

wp0708 : Base 4 → WsL → ⟪ (CX01 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX01 ∷ Toff204 ∷ []) ⟫ʷ
wp0708 c4 L = pw3 c4 L (CX01 ∷ Toff214 ∷ []) (Toff214 ∷ CX01 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0709 : Base 4 → WsL → ⟪ (CCZ023 ∷ Toff204 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ023 ∷ []) ⟫ʷ
wp0709 c4 L = pw1 c4 L (CCZ023 ∷ Toff204 ∷ CCZ034 ∷ []) (Toff204 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0710 : Base 4 → WsL → ⟪ (CX40 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX40 ∷ []) ⟫ʷ
wp0710 c4 L = pw3 c4 L (CX40 ∷ Toff214 ∷ []) (Toff214 ∷ CX40 ∷ []) tt tt Eq.refl

wp0711 : Base 4 → WsL → ⟪ (CX01 ∷ Toff204 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
wp0711 c4 L = pw3 c4 L (CX01 ∷ Toff204 ∷ Toff204 ∷ []) (CX01 ∷ []) tt tt Eq.refl

wp0712 : Base 4 → WsL → ⟪ (CCZ134 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ134 ∷ []) ⟫ʷ
wp0712 c4 L = pw2 c4 L (CCZ134 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0713 : Base 4 → WsL → ⟪ (CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wp0713 c4 L = pw2 c4 L (CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wp0714 : Base 4 → WsL → ⟪ (Sw01 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw01 ∷ []) ⟫ʷ
wp0714 c4 L = pw3 c4 L (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0715 : Base 4 → WsL → ⟪ (Sw01 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw01 ∷ []) ⟫ʷ
wp0715 c4 L = pw3 c4 L (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0716 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) ⟫ʷ
wp0716 c4 L = pw2 c4 L (CCZ034 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0717 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ024 ∷ []) ⟫ʷ
wp0717 c4 L = pw1 c4 L (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (CX32 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0718 : Base 4 → WsL → ⟪ (CX32 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
wp0718 c4 L = pw1 c4 L (CX32 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX32 ∷ []) tt tt Eq.refl

wp0719 : Base 4 → WsL → ⟪ (Sw23 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw23 ∷ []) ⟫ʷ
wp0719 c4 L = pw1 c4 L (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) tt tt Eq.refl

wp0720 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ014 ∷ []) ⟫ʷ
wp0720 c4 L = pw3 c4 L (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) (CX21 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0721 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) ⟫ʷ
wp0721 c4 L = pw1 c4 L (CCZ024 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0722 : Base 4 → WsL → ⟪ (CCZ014 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0722 c4 L = pw3 c4 L (CCZ014 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0723 : Base 4 → WsL → ⟪ (CX21 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wp0723 c4 L = pw3 c4 L (CX21 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX21 ∷ []) tt tt Eq.refl

wp0724 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff013 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ014 ∷ []) ⟫ʷ
wp0724 c4 L = pw2 c4 L (CCZ014 ∷ Toff013 ∷ CCZ134 ∷ []) (Toff013 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0725 : Base 4 → WsL → ⟪ (CS34 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS34 ∷ []) ⟫ʷ
wp0725 c4 L = pw1 c4 L (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ []) tt tt Eq.refl

wp0726 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0726 c4 L = pw1 c4 L (CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0727 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ024 ∷ CX41 ∷ []) ⟫ʷ
wp0727 c4 L = pw3 c4 L (CCZ024 ∷ []) (CX41 ∷ CCZ024 ∷ CX41 ∷ []) tt tt Eq.refl

wp0728 : Base 4 → WsL → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ012 ∷ CX14 ∷ []) ⟫ʷ
wp0728 c4 L = pw3 c4 L (CCZ012 ∷ []) (CX14 ∷ CCZ012 ∷ CX14 ∷ []) tt tt Eq.refl

wp0729 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) ⟫ʷ
wp0729 c4 L = pw3 c4 L (CCZ024 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0730 : Base 4 → WsL → ⟪ (CCZ012 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) ⟫ʷ
wp0730 c4 L = pw3 c4 L (CCZ012 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0731 : Base 4 → WsL → ⟪ (CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp0731 c4 L = pw3 c4 L (CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp0732 : Base 4 → WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) ⟫ʷ
wp0732 c4 L = pw1 c4 L (CCZ034 ∷ []) (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) tt tt Eq.refl

wp0733 : Base 4 → WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) ⟫ʷ
wp0733 c4 L = pw2 c4 L (CCZ034 ∷ []) (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) tt tt Eq.refl

wp0734 : Base 4 → WsL → ⟪ (CCZ034 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0734 c4 L = pw2 c4 L (CCZ034 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0735 : Base 4 → WsL → ⟪ (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ034 ∷ []) ⟫ʷ
wp0735 c4 L = pw2 c4 L (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (CX14 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0736 : Base 4 → WsL → ⟪ (CX14 ∷ CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wp0736 c4 L = pw2 c4 L (CX14 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wp0737 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ034 ∷ []) ⟫ʷ
wp0737 c4 L = pw1 c4 L (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) (Toff324 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0738 : Base 4 → WsL → ⟪ (CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wp0738 c4 L = pw3 c4 L (CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl

wp0739 : Base 4 → WsL → ⟪ (CCZ034 ∷ CCZ234 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ034 ∷ []) ⟫ʷ
wp0739 c4 L = pw1 c4 L (CCZ034 ∷ CCZ234 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0740 : Base 4 → WsL → ⟪ (K3⁻ ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ K3⁻ ∷ []) ⟫ʷ
wp0740 c4 L = pw1 c4 L (K3⁻ ∷ Toff024 ∷ []) (Toff024 ∷ K3⁻ ∷ []) tt tt Eq.refl

wp0741 : Base 4 → WsL → ⟪ (CS12⁻ ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0741 c4 L = pw3 c4 L (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0742 : Base 4 → WsL → ⟪ (K3 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ K3 ∷ []) ⟫ʷ
wp0742 c4 L = pw1 c4 L (K3 ∷ Toff024 ∷ []) (Toff024 ∷ K3 ∷ []) tt tt Eq.refl

wp0743 : Base 4 → WsL → ⟪ (CCZ124 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0743 c4 L = pw3 c4 L (CCZ124 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0744 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ024 ∷ []) ⟫ʷ
wp0744 c4 L = pw3 c4 L (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) (CX12 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0745 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ014 ∷ CCZ134 ∷ []) ⟫ʷ
wp0745 c4 L = pw2 c4 L (CCZ014 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0746 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0746 c4 L = pw3 c4 L (CCZ024 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0747 : Base 4 → WsL → ⟪ (CX12 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
wp0747 c4 L = pw3 c4 L (CX12 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX12 ∷ []) tt tt Eq.refl

wp0748 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff023 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ024 ∷ []) ⟫ʷ
wp0748 c4 L = pw1 c4 L (CCZ024 ∷ Toff023 ∷ CCZ234 ∷ []) (Toff023 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0749 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ024 ∷ []) ⟫ʷ
wp0749 c4 L = pw3 c4 L (CCZ024 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0750 : Base 4 → WsL → ⟪ (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ012 ∷ []) ⟫ʷ
wp0750 c4 L = pw3 c4 L (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) (Toff214 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0751 : Base 4 → WsL → ⟪ (K2⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ K2⁻ ∷ []) ⟫ʷ
wp0751 c4 L = pw1 c4 L (K2⁻ ∷ Toff034 ∷ []) (Toff034 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp0752 : Base 4 → WsL → ⟪ (K2 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ K2 ∷ []) ⟫ʷ
wp0752 c4 L = pw1 c4 L (K2 ∷ Toff034 ∷ []) (Toff034 ∷ K2 ∷ []) tt tt Eq.refl

wp0753 : Base 4 → WsL → ⟪ (Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
wp0753 c4 L = pw3 c4 L (Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff214 ∷ []) tt tt Eq.refl

wp0754 : Base 4 → WsL → ⟪ (CS02⁻ ∷ CX23 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff324 ∷ CS02⁻ ∷ []) ⟫ʷ
wp0754 c4 L = pw1 c4 L (CS02⁻ ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0755 : Base 4 → WsL → ⟪ (CS02 ∷ CX23 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff324 ∷ CS02 ∷ []) ⟫ʷ
wp0755 c4 L = pw1 c4 L (CS02 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CS02 ∷ []) tt tt Eq.refl

wp0756 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ024 ∷ []) ⟫ʷ
wp0756 c4 L = pw1 c4 L (CCZ024 ∷ CX03 ∷ []) (CX03 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0757 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ024 ∷ []) ⟫ʷ
wp0757 c4 L = pw1 c4 L (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) (CX30 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0758 : Base 4 → WsL → ⟪ (CX30 ∷ CCZ234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
wp0758 c4 L = pw1 c4 L (CX30 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX30 ∷ []) tt tt Eq.refl

wp0759 : Base 4 → WsL → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ134 ∷ CX30 ∷ []) ⟫ʷ
wp0759 c4 L = pw2 c4 L (CCZ134 ∷ []) (CX30 ∷ CCZ134 ∷ CX30 ∷ []) tt tt Eq.refl

wp0760 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ024 ∷ []) ⟫ʷ
wp0760 c4 L = pw3 c4 L (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (Toff201 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0761 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ014 ∷ CX03 ∷ []) ⟫ʷ
wp0761 c4 L = pw2 c4 L (CCZ014 ∷ []) (CX03 ∷ CCZ014 ∷ CX03 ∷ []) tt tt Eq.refl

wp0762 : Base 4 → WsL → ⟪ (CCZ134 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) ⟫ʷ
wp0762 c4 L = pw2 c4 L (CCZ134 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0763 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) ⟫ʷ
wp0763 c4 L = pw2 c4 L (CCZ014 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0764 : Base 4 → WsL → ⟪ (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wp0764 c4 L = pw2 c4 L (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wp0765 : Base 4 → WsL → ⟪ (CCZ234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ234 ∷ []) ⟫ʷ
wp0765 c4 L = pw1 c4 L (CCZ234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0766 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) ⟫ʷ
wp0766 c4 L = pw1 c4 L (CCZ024 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) tt tt Eq.refl

wp0767 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) ⟫ʷ
wp0767 c4 L = pw3 c4 L (CCZ024 ∷ []) (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) tt tt Eq.refl

wp0768 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ024 ∷ []) ⟫ʷ
wp0768 c4 L = pw1 c4 L (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (Toff234 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0769 : Base 4 → WsL → ⟪ (CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
wp0769 c4 L = pw2 c4 L (CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl

wp0770 : Base 4 → WsL → ⟪ (CCZ024 ∷ CCZ234 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0770 c4 L = pw1 c4 L (CCZ024 ∷ CCZ234 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0771 : Base 4 → WsL → ⟪ (CCZ013 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) ⟫ʷ
wp0771 c4 L = pw2 c4 L (CCZ013 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0772 : Base 4 → WsL → ⟪ (CS13⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS13⁻ ∷ []) ⟫ʷ
wp0772 c4 L = pw2 c4 L (CS13⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0773 : Base 4 → WsL → ⟪ (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ234 ∷ []) ⟫ʷ
wp0773 c4 L = pw1 c4 L (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) (CX03 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0774 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) ⟫ʷ
wp0774 c4 L = pw3 c4 L (CCZ024 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0775 : Base 4 → WsL → ⟪ (CX03 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
wp0775 c4 L = pw1 c4 L (CX03 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX03 ∷ []) tt tt Eq.refl

wp0776 : Base 4 → WsL → ⟪ (CCZ234 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ234 ∷ []) ⟫ʷ
wp0776 c4 L = pw1 c4 L (CCZ234 ∷ CX30 ∷ []) (CX30 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0777 : Base 4 → WsL → ⟪ (CS14 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS14 ∷ []) ⟫ʷ
wp0777 c4 L = pw3 c4 L (CS14 ∷ Toff201 ∷ []) (Toff201 ∷ CS14 ∷ []) tt tt Eq.refl

wp0778 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ014 ∷ []) ⟫ʷ
wp0778 c4 L = pw2 c4 L (CCZ014 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0779 : Base 4 → WsL → ⟪ (CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp0779 c4 L = pw2 c4 L (CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp0780 : Base 4 → WsL → ⟪ (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
wp0780 c4 L = pw1 c4 L (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0781 : Base 4 → WsL → ⟪ (CCZ024 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ Toff204 ∷ []) ⟫ʷ
wp0781 c4 L = pw1 c4 L (CCZ024 ∷ CZ04 ∷ []) (Toff204 ∷ CCZ024 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0782 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ CCZ024 ∷ CZ04 ∷ []) ⟫ʷ
wp0782 c4 L = pw1 c4 L (CCZ024 ∷ []) (CZ04 ∷ CCZ024 ∷ CZ04 ∷ []) tt tt Eq.refl

wp0783 : Base 4 → WsL → ⟪ (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff013 ∷ []) ⟫ʷ
wp0783 c4 L = pw2 c4 L (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) (Toff314 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0784 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ024 ∷ []) ⟫ʷ
wp0784 c4 L = pw3 c4 L (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) (Toff014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0785 : Base 4 → WsL → ⟪ (CS14 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS14 ∷ []) ⟫ʷ
wp0785 c4 L = pw2 c4 L (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ []) tt tt Eq.refl

wp0786 : Base 4 → WsL → ⟪ (Toff013 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff013 ∷ []) ⟫ʷ
wp0786 c4 L = pw2 c4 L (Toff013 ∷ Toff014 ∷ []) (Toff014 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0787 : Base 4 → WsL → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ124 ∷ Toff014 ∷ []) ⟫ʷ
wp0787 c4 L = pw3 c4 L (CCZ124 ∷ []) (Toff014 ∷ CCZ124 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0788 : Base 4 → WsL → ⟪ (CX31 ∷ Toff134 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX31 ∷ Toff134 ∷ []) ⟫ʷ
wp0788 c4 L = pw2 c4 L (CX31 ∷ Toff134 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX31 ∷ Toff134 ∷ []) tt tt Eq.refl

wp0789 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0789 c4 L = pw1 c4 L (CCZ024 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0790 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0790 c4 L = pw1 c4 L (CCZ024 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0791 : Base 4 → WsL → ⟪ (CX31 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Toff134 ∷ []) ⟫ʷ
wp0791 c4 L = pw2 c4 L (CX31 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) (CX31 ∷ Toff134 ∷ []) tt tt Eq.refl

wp0792 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ014 ∷ []) ⟫ʷ
wp0792 c4 L = pw2 c4 L (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) (CX31 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0793 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) ⟫ʷ
wp0793 c4 L = pw1 c4 L (CCZ034 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0794 : Base 4 → WsL → ⟪ (CX31 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
wp0794 c4 L = pw2 c4 L (CX31 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX31 ∷ []) tt tt Eq.refl

wp0795 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ014 ∷ []) ⟫ʷ
wp0795 c4 L = pw2 c4 L (CCZ014 ∷ CX13 ∷ []) (CX13 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0796 : Base 4 → WsL → ⟪ (CCZ034 ∷ X4 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ034 ∷ []) ⟫ʷ
wp0796 c4 L = pw1 c4 L (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (X4 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0797 : Base 4 → WsL → ⟪ (CCZ034 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CCZ034 ∷ []) ⟫ʷ
wp0797 c4 L = pw1 c4 L (CCZ034 ∷ CZ03 ∷ []) (CZ03 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0798 : Base 4 → WsL → ⟪ (X4 ∷ CZ03 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ []) ⟫ʷ
wp0798 c4 L = pw1 c4 L (X4 ∷ CZ03 ∷ CZ03 ∷ []) (X4 ∷ []) tt tt Eq.refl

wp0799 : Base 4 → WsL → ⟪ (CCZ012 ∷ CX12 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ []) ⟫ʷ
wp0799 c4 L = pw3 c4 L (CCZ012 ∷ CX12 ∷ Toff214 ∷ []) (CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0800 : Base 4 → WsL → ⟪ (CZ01 ∷ CCZ134 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ01 ∷ []) ⟫ʷ
wp0800 c4 L = pw2 c4 L (CZ01 ∷ CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CZ01 ∷ []) tt tt Eq.refl

wp0801 : Base 4 → WsL → ⟪ (CCZ014 ∷ CCZ134 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ014 ∷ []) ⟫ʷ
wp0801 c4 L = pw2 c4 L (CCZ014 ∷ CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0802 : Base 4 → WsL → ⟪ (CZ01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) ⟫ʷ
wp0802 c4 L = pw2 c4 L (CZ01 ∷ CCZ014 ∷ []) (CZ01 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0803 : Base 4 → WsL → ⟪ (CCZ012 ∷ CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff214 ∷ CCZ012 ∷ []) ⟫ʷ
wp0803 c4 L = pw3 c4 L (CCZ012 ∷ CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ []) (CX12 ∷ Toff214 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0804 : Base 4 → WsL → ⟪ (CS02⁻ ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS02⁻ ∷ []) ⟫ʷ
wp0804 c4 L = pw1 c4 L (CS02⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0805 : Base 4 → WsL → ⟪ (Toff023 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) ⟫ʷ
wp0805 c4 L = pw1 c4 L (Toff023 ∷ Toff324 ∷ []) (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0806 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) ⟫ʷ
wp0806 c4 L = pw3 c4 L (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0807 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX34 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ014 ∷ []) ⟫ʷ
wp0807 c4 L = pw2 c4 L (CCZ014 ∷ CX34 ∷ CCZ013 ∷ []) (CX34 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0808 : Base 4 → WsL → ⟪ (CX34 ∷ CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ []) ⟫ʷ
wp0808 c4 L = pw2 c4 L (CX34 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX34 ∷ []) tt tt Eq.refl

wp0809 : Base 4 → WsL → ⟪ (CX43 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX43 ∷ Toff024 ∷ []) ⟫ʷ
wp0809 c4 L = pw1 c4 L (CX43 ∷ Toff023 ∷ []) (Toff023 ∷ CX43 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0810 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ014 ∷ []) ⟫ʷ
wp0810 c4 L = pw2 c4 L (CCZ014 ∷ CX43 ∷ []) (CX43 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0811 : Base 4 → WsL → ⟪ (CX43 ∷ Toff024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ []) ⟫ʷ
wp0811 c4 L = pw1 c4 L (CX43 ∷ Toff024 ∷ Toff024 ∷ []) (CX43 ∷ []) tt tt Eq.refl

wp0812 : Base 4 → WsL → ⟪ (Sw34 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw34 ∷ []) ⟫ʷ
wp0812 c4 L = pw1 c4 L (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0813 : Base 4 → WsL → ⟪ (Sw34 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Sw34 ∷ []) ⟫ʷ
wp0813 c4 L = pw1 c4 L (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0814 : Base 4 → WsL → ⟪ (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ023 ∷ []) ⟫ʷ
wp0814 c4 L = pw1 c4 L (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (Toff324 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0815 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0815 c4 L = pw3 c4 L (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0816 : Base 4 → WsL → ⟪ (K3⁻ ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ K3⁻ ∷ []) ⟫ʷ
wp0816 c4 L = pw2 c4 L (K3⁻ ∷ Toff014 ∷ []) (Toff014 ∷ K3⁻ ∷ []) tt tt Eq.refl

wp0817 : Base 4 → WsL → ⟪ (CS24 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS24 ∷ []) ⟫ʷ
wp0817 c4 L = pw3 c4 L (CS24 ∷ Toff014 ∷ []) (Toff014 ∷ CS24 ∷ []) tt tt Eq.refl

wp0818 : Base 4 → WsL → ⟪ (CS34⁻ ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0818 c4 L = pw2 c4 L (CS34⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0819 : Base 4 → WsL → ⟪ (K3 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ K3 ∷ []) ⟫ʷ
wp0819 c4 L = pw2 c4 L (K3 ∷ Toff014 ∷ []) (Toff014 ∷ K3 ∷ []) tt tt Eq.refl

wp0820 : Base 4 → WsL → ⟪ (CCZ023 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wp0820 c4 L = pw1 c4 L (CCZ023 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0821 : Base 4 → WsL → ⟪ (Toff324 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
wp0821 c4 L = pw1 c4 L (Toff324 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff324 ∷ []) tt tt Eq.refl

wp0822 : Base 4 → WsL → ⟪ (CCZ124 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ124 ∷ []) ⟫ʷ
wp0822 c4 L = pw3 c4 L (CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0823 : Base 4 → WsL → ⟪ (CS34⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0823 c4 L = pw1 c4 L (CS34⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0824 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX31 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) ⟫ʷ
wp0824 c4 L = pw2 c4 L (CCZ014 ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0825 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ
wp0825 c4 L = pw2 c4 L (CCZ034 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0826 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff012 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ024 ∷ []) ⟫ʷ
wp0826 c4 L = pw3 c4 L (CCZ024 ∷ Toff012 ∷ CCZ124 ∷ []) (Toff012 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0827 : Base 4 → WsL → ⟪ (CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ024 ∷ []) ⟫ʷ
wp0827 c4 L = pw3 c4 L (CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0828 : Base 4 → WsL → ⟪ (CCZ013 ∷ Toff134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) ⟫ʷ
wp0828 c4 L = pw2 c4 L (CCZ013 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0829 : Base 4 → WsL → ⟪ (CCZ013 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ []) ⟫ʷ
wp0829 c4 L = pw2 c4 L (CCZ013 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0830 : Base 4 → WsL → ⟪ (CCZ013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ []) ⟫ʷ
wp0830 c4 L = pw2 c4 L (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0831 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ034 ∷ []) ⟫ʷ
wp0831 c4 L = pw2 c4 L (CCZ034 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0832 : Base 4 → WsL → ⟪ (Toff013 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) ⟫ʷ
wp0832 c4 L = pw2 c4 L (Toff013 ∷ Toff314 ∷ []) (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0833 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) ⟫ʷ
wp0833 c4 L = pw3 c4 L (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0834 : Base 4 → WsL → ⟪ (CS03⁻ ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0834 c4 L = pw2 c4 L (CS03⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0835 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ014 ∷ []) ⟫ʷ
wp0835 c4 L = pw2 c4 L (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0836 : Base 4 → WsL → ⟪ (Toff134 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ []) ⟫ʷ
wp0836 c4 L = pw2 c4 L (Toff134 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff134 ∷ []) tt tt Eq.refl

wp0837 : Base 4 → WsL → ⟪ (CCZ023 ∷ CX23 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ []) ⟫ʷ
wp0837 c4 L = pw1 c4 L (CCZ023 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0838 : Base 4 → WsL → ⟪ (CZ02 ∷ CCZ124 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CZ02 ∷ []) ⟫ʷ
wp0838 c4 L = pw3 c4 L (CZ02 ∷ CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CZ02 ∷ []) tt tt Eq.refl

wp0839 : Base 4 → WsL → ⟪ (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ024 ∷ []) ⟫ʷ
wp0839 c4 L = pw3 c4 L (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0840 : Base 4 → WsL → ⟪ (CZ02 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0840 c4 L = pw3 c4 L (CZ02 ∷ CCZ024 ∷ []) (CZ02 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0841 : Base 4 → WsL → ⟪ (CCZ023 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff324 ∷ CCZ023 ∷ []) ⟫ʷ
wp0841 c4 L = pw1 c4 L (CCZ023 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ []) (CX23 ∷ Toff324 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0842 : Base 4 → WsL → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) ⟫ʷ
wp0842 c4 L = pw1 c4 L (CCZ234 ∷ []) (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0843 : Base 4 → WsL → ⟪ (Toff013 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) ⟫ʷ
wp0843 c4 L = pw2 c4 L (Toff013 ∷ Toff134 ∷ []) (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0844 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ234 ∷ CCZ024 ∷ []) ⟫ʷ
wp0844 c4 L = pw1 c4 L (CCZ024 ∷ CX30 ∷ []) (CX30 ∷ CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0845 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) ⟫ʷ
wp0845 c4 L = pw1 c4 L (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0846 : Base 4 → WsL → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ234 ∷ CX30 ∷ []) ⟫ʷ
wp0846 c4 L = pw1 c4 L (CCZ234 ∷ []) (CX30 ∷ CCZ234 ∷ CX30 ∷ []) tt tt Eq.refl

wp0847 : Base 4 → WsL → ⟪ (CS04 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CS04 ∷ []) ⟫ʷ
wp0847 c4 L = pw1 c4 L (CS04 ∷ S4 ∷ []) (S4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0848 : Base 4 → WsL → ⟪ (CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CK40 ∷ []) ⟫ʷ
wp0848 c4 L = pw1 c4 L (CK40 ∷ S4 ∷ []) (S4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0849 : Base 4 → WsL → ⟪ (S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S4 ∷ []) ⟫ʷ
wp0849 c4 L = pw2 c4 L (S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S4 ∷ []) tt tt Eq.refl

wp0850 : Base 4 → WsL → ⟪ (CS04 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS04 ∷ []) ⟫ʷ
wp0850 c4 L = pw2 c4 L (CS04 ∷ CS14 ∷ []) (CS14 ∷ CS04 ∷ []) tt tt Eq.refl

wp0851 : Base 4 → WsL → ⟪ (CS04 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS04 ∷ []) ⟫ʷ
wp0851 c4 L = pw1 c4 L (CS04 ∷ CS24 ∷ []) (CS24 ∷ CS04 ∷ []) tt tt Eq.refl

wp0852 : Base 4 → WsL → ⟪ (CS04 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS04 ∷ []) ⟫ʷ
wp0852 c4 L = pw1 c4 L (CS04 ∷ CS34 ∷ []) (CS34 ∷ CS04 ∷ []) tt tt Eq.refl

wp0853 : Base 4 → WsL → ⟪ (CK41 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK41 ∷ []) ⟫ʷ
wp0853 c4 L = pw2 c4 L (CK41 ∷ CS04 ∷ []) (CS04 ∷ CK41 ∷ []) tt tt Eq.refl

wp0854 : Base 4 → WsL → ⟪ (CK42 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK42 ∷ []) ⟫ʷ
wp0854 c4 L = pw1 c4 L (CK42 ∷ CS04 ∷ []) (CS04 ∷ CK42 ∷ []) tt tt Eq.refl

wp0855 : Base 4 → WsL → ⟪ (CK43 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK43 ∷ []) ⟫ʷ
wp0855 c4 L = pw1 c4 L (CK43 ∷ CS04 ∷ []) (CS04 ∷ CK43 ∷ []) tt tt Eq.refl

wp0856 : Base 4 → WsL → ⟪ (CS04 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS04 ∷ []) ⟫ʷ
wp0856 c4 L = pw2 c4 L (CS04 ∷ CS13 ∷ []) (CS13 ∷ CS04 ∷ []) tt tt Eq.refl

wp0857 : Base 4 → WsL → ⟪ (CS04 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS04 ∷ []) ⟫ʷ
wp0857 c4 L = pw2 c4 L (CS04 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04 ∷ []) tt tt Eq.refl

wp0858 : Base 4 → WsL → ⟪ (CS04 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS04 ∷ []) ⟫ʷ
wp0858 c4 L = pw2 c4 L (CS04 ∷ Toff134 ∷ []) (Toff134 ∷ CS04 ∷ []) tt tt Eq.refl

wp0859 : Base 4 → WsL → ⟪ (CS04 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS04 ∷ []) ⟫ʷ
wp0859 c4 L = pw3 c4 L (CS04 ∷ CS12 ∷ []) (CS12 ∷ CS04 ∷ []) tt tt Eq.refl

wp0860 : Base 4 → WsL → ⟪ (CS04 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS04 ∷ []) ⟫ʷ
wp0860 c4 L = pw3 c4 L (CS04 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04 ∷ []) tt tt Eq.refl

wp0861 : Base 4 → WsL → ⟪ (CK40 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK40 ∷ []) ⟫ʷ
wp0861 c4 L = pw2 c4 L (CK40 ∷ CS14 ∷ []) (CS14 ∷ CK40 ∷ []) tt tt Eq.refl

wp0862 : Base 4 → WsL → ⟪ (CK40 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK40 ∷ []) ⟫ʷ
wp0862 c4 L = pw1 c4 L (CK40 ∷ CS24 ∷ []) (CS24 ∷ CK40 ∷ []) tt tt Eq.refl

wp0863 : Base 4 → WsL → ⟪ (CS03 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS03 ∷ []) ⟫ʷ
wp0863 c4 L = pw1 c4 L (CS03 ∷ CS24 ∷ []) (CS24 ∷ CS03 ∷ []) tt tt Eq.refl

wp0864 : Base 4 → WsL → ⟪ (CS03⁻ ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0864 c4 L = pw1 c4 L (CS03⁻ ∷ CS24 ∷ []) (CS24 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0865 : Base 4 → WsL → ⟪ (CK40 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK40 ∷ []) ⟫ʷ
wp0865 c4 L = pw1 c4 L (CK40 ∷ CS34 ∷ []) (CS34 ∷ CK40 ∷ []) tt tt Eq.refl

wp0866 : Base 4 → WsL → ⟪ (CS34 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS34 ∷ []) ⟫ʷ
wp0866 c4 L = pw2 c4 L (CS34 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS34 ∷ []) tt tt Eq.refl

wp0867 : Base 4 → WsL → ⟪ (CK40 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK40 ∷ []) ⟫ʷ
wp0867 c4 L = pw2 c4 L (CK40 ∷ CK41 ∷ []) (CK41 ∷ CK40 ∷ []) tt tt Eq.refl

wp0868 : Base 4 → WsL → ⟪ (CK40 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK40 ∷ []) ⟫ʷ
wp0868 c4 L = pw1 c4 L (CK40 ∷ CK42 ∷ []) (CK42 ∷ CK40 ∷ []) tt tt Eq.refl

wp0869 : Base 4 → WsL → ⟪ (CK40 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK40 ∷ []) ⟫ʷ
wp0869 c4 L = pw1 c4 L (CK40 ∷ CK43 ∷ []) (CK43 ∷ CK40 ∷ []) tt tt Eq.refl

wp0870 : Base 4 → WsL → ⟪ (CK40 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CK40 ∷ []) ⟫ʷ
wp0870 c4 L = pw1 c4 L (CK40 ∷ Toff324 ∷ []) (Toff324 ∷ CK40 ∷ []) tt tt Eq.refl

wp0871 : Base 4 → WsL → ⟪ (CK40 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CK40 ∷ []) ⟫ʷ
wp0871 c4 L = pw2 c4 L (CK40 ∷ CS13 ∷ []) (CS13 ∷ CK40 ∷ []) tt tt Eq.refl

wp0872 : Base 4 → WsL → ⟪ (CK40 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CK40 ∷ []) ⟫ʷ
wp0872 c4 L = pw2 c4 L (CK40 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CK40 ∷ []) tt tt Eq.refl

wp0873 : Base 4 → WsL → ⟪ (CK40 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CK40 ∷ []) ⟫ʷ
wp0873 c4 L = pw2 c4 L (CK40 ∷ Toff134 ∷ []) (Toff134 ∷ CK40 ∷ []) tt tt Eq.refl

wp0874 : Base 4 → WsL → ⟪ (CK40 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CK40 ∷ []) ⟫ʷ
wp0874 c4 L = pw3 c4 L (CK40 ∷ CS12 ∷ []) (CS12 ∷ CK40 ∷ []) tt tt Eq.refl

wp0875 : Base 4 → WsL → ⟪ (CK40 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CK40 ∷ []) ⟫ʷ
wp0875 c4 L = pw3 c4 L (CK40 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK40 ∷ []) tt tt Eq.refl

wp0876 : Base 4 → WsL → ⟪ (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ014 ∷ []) ⟫ʷ
wp0876 c4 L = pw2 c4 L (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) (CK41 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0877 : Base 4 → WsL → ⟪ (CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CK41 ∷ []) ⟫ʷ
wp0877 c4 L = pw2 c4 L (CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ []) (CZ01 ∷ CK41 ∷ []) tt tt Eq.refl

wp0878 : Base 4 → WsL → ⟪ (CK42 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CK42 ∷ []) ⟫ʷ
wp0878 c4 L = pw1 c4 L (CK42 ∷ CS03 ∷ []) (CS03 ∷ CK42 ∷ []) tt tt Eq.refl

wp0879 : Base 4 → WsL → ⟪ (CK42 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CK42 ∷ []) ⟫ʷ
wp0879 c4 L = pw1 c4 L (CK42 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CK42 ∷ []) tt tt Eq.refl

wp0880 : Base 4 → WsL → ⟪ (CCZ013 ∷ CK43 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK43 ∷ []) ⟫ʷ
wp0880 c4 L = pw2 c4 L (CCZ013 ∷ CK43 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK43 ∷ []) tt tt Eq.refl

wp0881 : Base 4 → WsL → ⟪ (CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CCZ034 ∷ []) ⟫ʷ
wp0881 c4 L = pw1 c4 L (CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ []) (CK43 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0882 : Base 4 → WsL → ⟪ (CZ03 ∷ CK43 ∷ CZ03 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CK43 ∷ []) ⟫ʷ
wp0882 c4 L = pw1 c4 L (CZ03 ∷ CK43 ∷ CZ03 ∷ CZ03 ∷ []) (CZ03 ∷ CK43 ∷ []) tt tt Eq.refl

wp0883 : Base 4 → WsL → ⟪ (CCZ034 ∷ CCZ014 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ034 ∷ []) ⟫ʷ
wp0883 c4 L = pw2 c4 L (CCZ034 ∷ CCZ014 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0884 : Base 4 → WsL → ⟪ (CCZ034 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ034 ∷ Toff301 ∷ []) ⟫ʷ
wp0884 c4 L = pw2 c4 L (CCZ034 ∷ CCZ014 ∷ []) (Toff301 ∷ CCZ034 ∷ Toff301 ∷ []) tt tt Eq.refl

wp0885 : Base 4 → WsL → ⟪ (CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0885 c4 L = pw2 c4 L (CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0886 : Base 4 → WsL → ⟪ (CZ01 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CZ01 ∷ CCZ124 ∷ []) ⟫ʷ
wp0886 c4 L = pw3 c4 L (CZ01 ∷ Toff024 ∷ []) (Toff024 ∷ CZ01 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0887 : Base 4 → WsL → ⟪ (Toff024 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff024 ∷ []) ⟫ʷ
wp0887 c4 L = pw1 c4 L (Toff024 ∷ X3 ∷ []) (X3 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0888 : Base 4 → WsL → ⟪ (CCZ034 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ
wp0888 c4 L = pw1 c4 L (CCZ034 ∷ K4 ∷ []) (K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0889 : Base 4 → WsL → ⟪ (CCZ034 ∷ CK34 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ CK34 ∷ CZ04 ∷ CCZ034 ∷ []) ⟫ʷ
wp0889 c4 L = pw1 c4 L (CCZ034 ∷ CK34 ∷ []) (CZ04 ∷ CK34 ∷ CZ04 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0890 : Base 4 → WsL → ⟪ (CCZ034 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CCZ034 ∷ []) ⟫ʷ
wp0890 c4 L = pw1 c4 L (CCZ034 ∷ S3 ∷ []) (S3 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0891 : Base 4 → WsL → ⟪ (K4 ∷ CK34 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ S3 ∷ []) ⟫ʷ
wp0891 c4 L = pw1 c4 L (K4 ∷ CK34 ∷ S3 ∷ []) (K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ S3 ∷ []) tt tt Eq.refl

wp0892 : Base 4 → WsL → ⟪ (K4 ∷ CK34 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ ι ∷ []) ⟫ʷ
wp0892 c4 L = pw1 c4 L (K4 ∷ CK34 ∷ ι ∷ []) (K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ ι ∷ []) tt tt Eq.refl

wp0893 : Base 4 → WsL → ⟪ (CCZ124 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ ι1 ∷ CCZ124 ∷ []) ⟫ʷ
wp0893 c4 L = pw0 c4 L (CCZ124 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ X3 ∷ []) (X3 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ ι1 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0894 : Base 4 → WsL → ⟪ (Toff402 ∷ CS14 ∷ Toff402 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0894 c4 L = pw3 c4 L (Toff402 ∷ CS14 ∷ Toff402 ∷ CS14⁻ ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0895 : Base 4 → WsL → ⟪ (CCZ134 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ134 ∷ CCZ014 ∷ []) ⟫ʷ
wp0895 c4 L = pw2 c4 L (CCZ134 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ134 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0896 : Base 4 → WsL → ⟪ (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ234 ∷ []) ⟫ʷ
wp0896 c4 L = pw1 c4 L (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (Toff302 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0897 : Base 4 → WsL → ⟪ (CS04 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS04 ∷ []) ⟫ʷ
wp0897 c4 L = pw2 c4 L (CS04 ∷ Toff301 ∷ []) (Toff301 ∷ CS04 ∷ []) tt tt Eq.refl

wp0898 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ024 ∷ CX21 ∷ []) ⟫ʷ
wp0898 c4 L = pw3 c4 L (CCZ024 ∷ []) (CX21 ∷ CCZ024 ∷ CX21 ∷ []) tt tt Eq.refl

wp0899 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) ⟫ʷ
wp0899 c4 L = pw3 c4 L (CCZ014 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0900 : Base 4 → WsL → ⟪ (CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp0900 c4 L = pw3 c4 L (CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp0901 : Base 4 → WsL → ⟪ (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0901 c4 L = pw3 c4 L (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0902 : Base 4 → WsL → ⟪ (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0902 c4 L = pw1 c4 L (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) [] tt tt Eq.refl

wp0903 : Base 4 → WsL → ⟪ (CK40 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wp0903 c4 L = pw1 c4 L (CK40 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wp0904 : Base 4 → WsL → ⟪ (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wp0904 c4 L = pw1 c4 L (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wp0905 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0905 c4 L = pw2 c4 L (CCZ014 ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0906 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ024 ∷ []) ⟫ʷ
wp0906 c4 L = pw1 c4 L (CCZ024 ∷ CS04 ∷ []) (CS04 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0907 : Base 4 → WsL → ⟪ (CS04 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ []) ⟫ʷ
wp0907 c4 L = pw2 c4 L (CS04 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ []) tt tt Eq.refl

wp0908 : Base 4 → WsL → ⟪ (CCZ014 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ014 ∷ []) ⟫ʷ
wp0908 c4 L = pw2 c4 L (CCZ014 ∷ CS14 ∷ []) (CS14 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0909 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ024 ∷ []) ⟫ʷ
wp0909 c4 L = pw1 c4 L (CCZ024 ∷ CS24 ∷ []) (CS24 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0910 : Base 4 → WsL → ⟪ (CS14 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ []) ⟫ʷ
wp0910 c4 L = pw2 c4 L (CS14 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ []) tt tt Eq.refl

wp0911 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ024 ∷ []) ⟫ʷ
wp0911 c4 L = pw1 c4 L (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (CX34 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0912 : Base 4 → WsL → ⟪ (CX34 ∷ CCZ023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ []) ⟫ʷ
wp0912 c4 L = pw1 c4 L (CX34 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX34 ∷ []) tt tt Eq.refl

wp0913 : Base 4 → WsL → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ013 ∷ CX34 ∷ []) ⟫ʷ
wp0913 c4 L = pw2 c4 L (CCZ013 ∷ []) (CX34 ∷ CCZ013 ∷ CX34 ∷ []) tt tt Eq.refl

wp0914 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ024 ∷ []) ⟫ʷ
wp0914 c4 L = pw1 c4 L (CCZ024 ∷ CX43 ∷ []) (CX43 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0915 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ014 ∷ CX43 ∷ []) ⟫ʷ
wp0915 c4 L = pw2 c4 L (CCZ014 ∷ []) (CX43 ∷ CCZ014 ∷ CX43 ∷ []) tt tt Eq.refl

wp0916 : Base 4 → WsL → ⟪ (CCZ013 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) ⟫ʷ
wp0916 c4 L = pw2 c4 L (CCZ013 ∷ CX43 ∷ []) (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0917 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) ⟫ʷ
wp0917 c4 L = pw2 c4 L (CCZ014 ∷ CX34 ∷ []) (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0918 : Base 4 → WsL → ⟪ (CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
wp0918 c4 L = pw2 c4 L (CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl

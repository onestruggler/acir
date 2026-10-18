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

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp0675 : Complete 4 → ⟪ (CCZ034 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ134 ∷ []) ⟫ʷ
wp0675 c4 = pw2 c4 (CCZ034 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0676 : Complete 4 → ⟪ (Sw01 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw01 ∷ []) ⟫ʷ
wp0676 c4 = pw2 c4 (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0677 : Complete 4 → ⟪ (CCZ134 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ034 ∷ []) ⟫ʷ
wp0677 c4 = pw2 c4 (CCZ134 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0678 : Complete 4 → ⟪ (Sw01 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sw01 ∷ []) ⟫ʷ
wp0678 c4 = pw2 c4 (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0679 : Complete 4 → ⟪ (CCZ124 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ124 ∷ []) ⟫ʷ
wp0679 c4 = pw3 c4 (CCZ124 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0680 : Complete 4 → ⟪ (CCZ023 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ023 ∷ []) ⟫ʷ
wp0680 c4 = pw1 c4 (CCZ023 ∷ CX34 ∷ []) (CX34 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0681 : Complete 4 → ⟪ (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ []) ⟫ʷ
wp0681 c4 = pw1 c4 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl

wp0682 : Complete 4 → ⟪ (CS04⁻ ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0682 c4 = pw3 c4 (CS04⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0683 : Complete 4 → ⟪ (CS04 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS04 ∷ []) ⟫ʷ
wp0683 c4 = pw3 c4 (CS04 ∷ Toff214 ∷ []) (Toff214 ∷ CS04 ∷ []) tt tt Eq.refl

wp0684 : Complete 4 → ⟪ (CCZ023 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ CCZ023 ∷ []) ⟫ʷ
wp0684 c4 = pw1 c4 (CCZ023 ∷ CX04 ∷ []) (CX04 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0685 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ
wp0685 c4 = pw3 c4 (CCZ014 ∷ []) (CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0686 : Complete 4 → ⟪ (CCZ014 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ014 ∷ []) ⟫ʷ
wp0686 c4 = pw3 c4 (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0687 : Complete 4 → ⟪ (CCZ014 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ014 ∷ []) ⟫ʷ
wp0687 c4 = pw2 c4 (CCZ014 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0688 : Complete 4 → ⟪ (CX01 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX01 ∷ []) ⟫ʷ
wp0688 c4 = pw2 c4 (CX01 ∷ Toff304 ∷ []) (Toff304 ∷ CX01 ∷ []) tt tt Eq.refl

wp0689 : Complete 4 → ⟪ (CCZ023 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ023 ∷ CCZ024 ∷ []) ⟫ʷ
wp0689 c4 = pw1 c4 (CCZ023 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0690 : Complete 4 → ⟪ (CX10 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX10 ∷ Toff314 ∷ []) ⟫ʷ
wp0690 c4 = pw2 c4 (CX10 ∷ Toff304 ∷ []) (Toff304 ∷ CX10 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0691 : Complete 4 → ⟪ (CS24 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS24 ∷ []) ⟫ʷ
wp0691 c4 = pw1 c4 (CS24 ∷ Toff304 ∷ []) (Toff304 ∷ CS24 ∷ []) tt tt Eq.refl

wp0692 : Complete 4 → ⟪ (CX41 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX41 ∷ []) ⟫ʷ
wp0692 c4 = pw2 c4 (CX41 ∷ Toff304 ∷ []) (Toff304 ∷ CX41 ∷ []) tt tt Eq.refl

wp0693 : Complete 4 → ⟪ (CX10 ∷ Toff314 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wp0693 c4 = pw2 c4 (CX10 ∷ Toff314 ∷ Toff314 ∷ []) (CX10 ∷ []) tt tt Eq.refl

wp0694 : Complete 4 → ⟪ (CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp0694 c4 = pw3 c4 (CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp0695 : Complete 4 → ⟪ (Sw01 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sw01 ∷ []) ⟫ʷ
wp0695 c4 = pw2 c4 (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0696 : Complete 4 → ⟪ (Sw01 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw01 ∷ []) ⟫ʷ
wp0696 c4 = pw2 c4 (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0697 : Complete 4 → ⟪ (CZ02 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CZ02 ∷ CCZ014 ∷ []) ⟫ʷ
wp0697 c4 = pw3 c4 (CZ02 ∷ Toff214 ∷ []) (Toff214 ∷ CZ02 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0698 : Complete 4 → ⟪ (CCZ014 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ []) ⟫ʷ
wp0698 c4 = pw2 c4 (CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0699 : Complete 4 → ⟪ (CCZ014 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ014 ∷ []) ⟫ʷ
wp0699 c4 = pw3 c4 (CCZ014 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0700 : Complete 4 → ⟪ (CCZ034 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0700 c4 = pw1 c4 (CCZ034 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0701 : Complete 4 → ⟪ (CCZ034 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CCZ034 ∷ []) ⟫ʷ
wp0701 c4 = pw1 c4 (CCZ034 ∷ K2 ∷ []) (K2 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0702 : Complete 4 → ⟪ (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ034 ∷ []) ⟫ʷ
wp0702 c4 = pw2 c4 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (Toff314 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0703 : Complete 4 → ⟪ (CS02⁻ ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wp0703 c4 = pw3 c4 (CS02⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0704 : Complete 4 → ⟪ (CCZ134 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ134 ∷ []) ⟫ʷ
wp0704 c4 = pw2 c4 (CCZ134 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0705 : Complete 4 → ⟪ (CCZ134 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ134 ∷ []) ⟫ʷ
wp0705 c4 = pw2 c4 (CCZ134 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0706 : Complete 4 → ⟪ (CCZ134 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ134 ∷ []) ⟫ʷ
wp0706 c4 = pw2 c4 (CCZ134 ∷ CS03 ∷ []) (CS03 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0707 : Complete 4 → ⟪ (CX10 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX10 ∷ []) ⟫ʷ
wp0707 c4 = pw3 c4 (CX10 ∷ Toff214 ∷ []) (Toff214 ∷ CX10 ∷ []) tt tt Eq.refl

wp0708 : Complete 4 → ⟪ (CX01 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX01 ∷ Toff204 ∷ []) ⟫ʷ
wp0708 c4 = pw3 c4 (CX01 ∷ Toff214 ∷ []) (Toff214 ∷ CX01 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0709 : Complete 4 → ⟪ (CCZ023 ∷ Toff204 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ023 ∷ []) ⟫ʷ
wp0709 c4 = pw1 c4 (CCZ023 ∷ Toff204 ∷ CCZ034 ∷ []) (Toff204 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0710 : Complete 4 → ⟪ (CX40 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX40 ∷ []) ⟫ʷ
wp0710 c4 = pw3 c4 (CX40 ∷ Toff214 ∷ []) (Toff214 ∷ CX40 ∷ []) tt tt Eq.refl

wp0711 : Complete 4 → ⟪ (CX01 ∷ Toff204 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
wp0711 c4 = pw3 c4 (CX01 ∷ Toff204 ∷ Toff204 ∷ []) (CX01 ∷ []) tt tt Eq.refl

wp0712 : Complete 4 → ⟪ (CCZ134 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ134 ∷ []) ⟫ʷ
wp0712 c4 = pw2 c4 (CCZ134 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0713 : Complete 4 → ⟪ (CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wp0713 c4 = pw2 c4 (CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wp0714 : Complete 4 → ⟪ (Sw01 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw01 ∷ []) ⟫ʷ
wp0714 c4 = pw3 c4 (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0715 : Complete 4 → ⟪ (Sw01 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw01 ∷ []) ⟫ʷ
wp0715 c4 = pw3 c4 (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) tt tt Eq.refl

wp0716 : Complete 4 → ⟪ (CCZ034 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) ⟫ʷ
wp0716 c4 = pw2 c4 (CCZ034 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0717 : Complete 4 → ⟪ (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ024 ∷ []) ⟫ʷ
wp0717 c4 = pw1 c4 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (CX32 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0718 : Complete 4 → ⟪ (CX32 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
wp0718 c4 = pw1 c4 (CX32 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX32 ∷ []) tt tt Eq.refl

wp0719 : Complete 4 → ⟪ (Sw23 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw23 ∷ []) ⟫ʷ
wp0719 c4 = pw1 c4 (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) tt tt Eq.refl

wp0720 : Complete 4 → ⟪ (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ014 ∷ []) ⟫ʷ
wp0720 c4 = pw3 c4 (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) (CX21 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0721 : Complete 4 → ⟪ (CCZ024 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) ⟫ʷ
wp0721 c4 = pw1 c4 (CCZ024 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0722 : Complete 4 → ⟪ (CCZ014 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0722 c4 = pw3 c4 (CCZ014 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0723 : Complete 4 → ⟪ (CX21 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wp0723 c4 = pw3 c4 (CX21 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX21 ∷ []) tt tt Eq.refl

wp0724 : Complete 4 → ⟪ (CCZ014 ∷ Toff013 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ014 ∷ []) ⟫ʷ
wp0724 c4 = pw2 c4 (CCZ014 ∷ Toff013 ∷ CCZ134 ∷ []) (Toff013 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0725 : Complete 4 → ⟪ (CS34 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS34 ∷ []) ⟫ʷ
wp0725 c4 = pw1 c4 (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ []) tt tt Eq.refl

wp0726 : Complete 4 → ⟪ (CCZ034 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0726 c4 = pw1 c4 (CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0727 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ024 ∷ CX41 ∷ []) ⟫ʷ
wp0727 c4 = pw3 c4 (CCZ024 ∷ []) (CX41 ∷ CCZ024 ∷ CX41 ∷ []) tt tt Eq.refl

wp0728 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ012 ∷ CX14 ∷ []) ⟫ʷ
wp0728 c4 = pw3 c4 (CCZ012 ∷ []) (CX14 ∷ CCZ012 ∷ CX14 ∷ []) tt tt Eq.refl

wp0729 : Complete 4 → ⟪ (CCZ024 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) ⟫ʷ
wp0729 c4 = pw3 c4 (CCZ024 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0730 : Complete 4 → ⟪ (CCZ012 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) ⟫ʷ
wp0730 c4 = pw3 c4 (CCZ012 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0731 : Complete 4 → ⟪ (CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp0731 c4 = pw3 c4 (CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp0732 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) ⟫ʷ
wp0732 c4 = pw1 c4 (CCZ034 ∷ []) (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) tt tt Eq.refl

wp0733 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) ⟫ʷ
wp0733 c4 = pw2 c4 (CCZ034 ∷ []) (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) tt tt Eq.refl

wp0734 : Complete 4 → ⟪ (CCZ034 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0734 c4 = pw2 c4 (CCZ034 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0735 : Complete 4 → ⟪ (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ034 ∷ []) ⟫ʷ
wp0735 c4 = pw2 c4 (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (CX14 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0736 : Complete 4 → ⟪ (CX14 ∷ CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wp0736 c4 = pw2 c4 (CX14 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wp0737 : Complete 4 → ⟪ (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ034 ∷ []) ⟫ʷ
wp0737 c4 = pw1 c4 (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) (Toff324 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0738 : Complete 4 → ⟪ (CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wp0738 c4 = pw3 c4 (CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl

wp0739 : Complete 4 → ⟪ (CCZ034 ∷ CCZ234 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ034 ∷ []) ⟫ʷ
wp0739 c4 = pw1 c4 (CCZ034 ∷ CCZ234 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0740 : Complete 4 → ⟪ (K3⁻ ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ K3⁻ ∷ []) ⟫ʷ
wp0740 c4 = pw1 c4 (K3⁻ ∷ Toff024 ∷ []) (Toff024 ∷ K3⁻ ∷ []) tt tt Eq.refl

wp0741 : Complete 4 → ⟪ (CS12⁻ ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0741 c4 = pw3 c4 (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0742 : Complete 4 → ⟪ (K3 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ K3 ∷ []) ⟫ʷ
wp0742 c4 = pw1 c4 (K3 ∷ Toff024 ∷ []) (Toff024 ∷ K3 ∷ []) tt tt Eq.refl

wp0743 : Complete 4 → ⟪ (CCZ124 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0743 c4 = pw3 c4 (CCZ124 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0744 : Complete 4 → ⟪ (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ024 ∷ []) ⟫ʷ
wp0744 c4 = pw3 c4 (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) (CX12 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0745 : Complete 4 → ⟪ (CCZ014 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ014 ∷ CCZ134 ∷ []) ⟫ʷ
wp0745 c4 = pw2 c4 (CCZ014 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0746 : Complete 4 → ⟪ (CCZ024 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0746 c4 = pw3 c4 (CCZ024 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0747 : Complete 4 → ⟪ (CX12 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
wp0747 c4 = pw3 c4 (CX12 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX12 ∷ []) tt tt Eq.refl

wp0748 : Complete 4 → ⟪ (CCZ024 ∷ Toff023 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ024 ∷ []) ⟫ʷ
wp0748 c4 = pw1 c4 (CCZ024 ∷ Toff023 ∷ CCZ234 ∷ []) (Toff023 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0749 : Complete 4 → ⟪ (CCZ024 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ024 ∷ []) ⟫ʷ
wp0749 c4 = pw3 c4 (CCZ024 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0750 : Complete 4 → ⟪ (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ012 ∷ []) ⟫ʷ
wp0750 c4 = pw3 c4 (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) (Toff214 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0751 : Complete 4 → ⟪ (K2⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ K2⁻ ∷ []) ⟫ʷ
wp0751 c4 = pw1 c4 (K2⁻ ∷ Toff034 ∷ []) (Toff034 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp0752 : Complete 4 → ⟪ (K2 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ K2 ∷ []) ⟫ʷ
wp0752 c4 = pw1 c4 (K2 ∷ Toff034 ∷ []) (Toff034 ∷ K2 ∷ []) tt tt Eq.refl

wp0753 : Complete 4 → ⟪ (Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
wp0753 c4 = pw3 c4 (Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff214 ∷ []) tt tt Eq.refl

wp0754 : Complete 4 → ⟪ (CS02⁻ ∷ CX23 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff324 ∷ CS02⁻ ∷ []) ⟫ʷ
wp0754 c4 = pw1 c4 (CS02⁻ ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0755 : Complete 4 → ⟪ (CS02 ∷ CX23 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff324 ∷ CS02 ∷ []) ⟫ʷ
wp0755 c4 = pw1 c4 (CS02 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CS02 ∷ []) tt tt Eq.refl

wp0756 : Complete 4 → ⟪ (CCZ024 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ024 ∷ []) ⟫ʷ
wp0756 c4 = pw1 c4 (CCZ024 ∷ CX03 ∷ []) (CX03 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0757 : Complete 4 → ⟪ (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ024 ∷ []) ⟫ʷ
wp0757 c4 = pw1 c4 (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) (CX30 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0758 : Complete 4 → ⟪ (CX30 ∷ CCZ234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
wp0758 c4 = pw1 c4 (CX30 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX30 ∷ []) tt tt Eq.refl

wp0759 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ134 ∷ CX30 ∷ []) ⟫ʷ
wp0759 c4 = pw2 c4 (CCZ134 ∷ []) (CX30 ∷ CCZ134 ∷ CX30 ∷ []) tt tt Eq.refl

wp0760 : Complete 4 → ⟪ (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ024 ∷ []) ⟫ʷ
wp0760 c4 = pw3 c4 (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (Toff201 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0761 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ014 ∷ CX03 ∷ []) ⟫ʷ
wp0761 c4 = pw2 c4 (CCZ014 ∷ []) (CX03 ∷ CCZ014 ∷ CX03 ∷ []) tt tt Eq.refl

wp0762 : Complete 4 → ⟪ (CCZ134 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) ⟫ʷ
wp0762 c4 = pw2 c4 (CCZ134 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0763 : Complete 4 → ⟪ (CCZ014 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) ⟫ʷ
wp0763 c4 = pw2 c4 (CCZ014 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0764 : Complete 4 → ⟪ (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wp0764 c4 = pw2 c4 (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wp0765 : Complete 4 → ⟪ (CCZ234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ234 ∷ []) ⟫ʷ
wp0765 c4 = pw1 c4 (CCZ234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0766 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) ⟫ʷ
wp0766 c4 = pw1 c4 (CCZ024 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) tt tt Eq.refl

wp0767 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) ⟫ʷ
wp0767 c4 = pw3 c4 (CCZ024 ∷ []) (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) tt tt Eq.refl

wp0768 : Complete 4 → ⟪ (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ024 ∷ []) ⟫ʷ
wp0768 c4 = pw1 c4 (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (Toff234 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0769 : Complete 4 → ⟪ (CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
wp0769 c4 = pw2 c4 (CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl

wp0770 : Complete 4 → ⟪ (CCZ024 ∷ CCZ234 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0770 c4 = pw1 c4 (CCZ024 ∷ CCZ234 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0771 : Complete 4 → ⟪ (CCZ013 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) ⟫ʷ
wp0771 c4 = pw2 c4 (CCZ013 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0772 : Complete 4 → ⟪ (CS13⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS13⁻ ∷ []) ⟫ʷ
wp0772 c4 = pw2 c4 (CS13⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0773 : Complete 4 → ⟪ (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ234 ∷ []) ⟫ʷ
wp0773 c4 = pw1 c4 (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) (CX03 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0774 : Complete 4 → ⟪ (CCZ024 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) ⟫ʷ
wp0774 c4 = pw3 c4 (CCZ024 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0775 : Complete 4 → ⟪ (CX03 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
wp0775 c4 = pw1 c4 (CX03 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX03 ∷ []) tt tt Eq.refl

wp0776 : Complete 4 → ⟪ (CCZ234 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ234 ∷ []) ⟫ʷ
wp0776 c4 = pw1 c4 (CCZ234 ∷ CX30 ∷ []) (CX30 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0777 : Complete 4 → ⟪ (CS14 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS14 ∷ []) ⟫ʷ
wp0777 c4 = pw3 c4 (CS14 ∷ Toff201 ∷ []) (Toff201 ∷ CS14 ∷ []) tt tt Eq.refl

wp0778 : Complete 4 → ⟪ (CCZ014 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ014 ∷ []) ⟫ʷ
wp0778 c4 = pw2 c4 (CCZ014 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0779 : Complete 4 → ⟪ (CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp0779 c4 = pw2 c4 (CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp0780 : Complete 4 → ⟪ (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
wp0780 c4 = pw1 c4 (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0781 : Complete 4 → ⟪ (CCZ024 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ Toff204 ∷ []) ⟫ʷ
wp0781 c4 = pw1 c4 (CCZ024 ∷ CZ04 ∷ []) (Toff204 ∷ CCZ024 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0782 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ CCZ024 ∷ CZ04 ∷ []) ⟫ʷ
wp0782 c4 = pw1 c4 (CCZ024 ∷ []) (CZ04 ∷ CCZ024 ∷ CZ04 ∷ []) tt tt Eq.refl

wp0783 : Complete 4 → ⟪ (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff013 ∷ []) ⟫ʷ
wp0783 c4 = pw2 c4 (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) (Toff314 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0784 : Complete 4 → ⟪ (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ024 ∷ []) ⟫ʷ
wp0784 c4 = pw3 c4 (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) (Toff014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0785 : Complete 4 → ⟪ (CS14 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS14 ∷ []) ⟫ʷ
wp0785 c4 = pw2 c4 (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ []) tt tt Eq.refl

wp0786 : Complete 4 → ⟪ (Toff013 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff013 ∷ []) ⟫ʷ
wp0786 c4 = pw2 c4 (Toff013 ∷ Toff014 ∷ []) (Toff014 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0787 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ124 ∷ Toff014 ∷ []) ⟫ʷ
wp0787 c4 = pw3 c4 (CCZ124 ∷ []) (Toff014 ∷ CCZ124 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0788 : Complete 4 → ⟪ (CX31 ∷ Toff134 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX31 ∷ Toff134 ∷ []) ⟫ʷ
wp0788 c4 = pw2 c4 (CX31 ∷ Toff134 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX31 ∷ Toff134 ∷ []) tt tt Eq.refl

wp0789 : Complete 4 → ⟪ (CCZ024 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0789 c4 = pw1 c4 (CCZ024 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0790 : Complete 4 → ⟪ (CCZ024 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0790 c4 = pw1 c4 (CCZ024 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0791 : Complete 4 → ⟪ (CX31 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Toff134 ∷ []) ⟫ʷ
wp0791 c4 = pw2 c4 (CX31 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) (CX31 ∷ Toff134 ∷ []) tt tt Eq.refl

wp0792 : Complete 4 → ⟪ (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ014 ∷ []) ⟫ʷ
wp0792 c4 = pw2 c4 (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) (CX31 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0793 : Complete 4 → ⟪ (CCZ034 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) ⟫ʷ
wp0793 c4 = pw1 c4 (CCZ034 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0794 : Complete 4 → ⟪ (CX31 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
wp0794 c4 = pw2 c4 (CX31 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX31 ∷ []) tt tt Eq.refl

wp0795 : Complete 4 → ⟪ (CCZ014 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ014 ∷ []) ⟫ʷ
wp0795 c4 = pw2 c4 (CCZ014 ∷ CX13 ∷ []) (CX13 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0796 : Complete 4 → ⟪ (CCZ034 ∷ X4 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ034 ∷ []) ⟫ʷ
wp0796 c4 = pw1 c4 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (X4 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0797 : Complete 4 → ⟪ (CCZ034 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CCZ034 ∷ []) ⟫ʷ
wp0797 c4 = pw1 c4 (CCZ034 ∷ CZ03 ∷ []) (CZ03 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0798 : Complete 4 → ⟪ (X4 ∷ CZ03 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ []) ⟫ʷ
wp0798 c4 = pw1 c4 (X4 ∷ CZ03 ∷ CZ03 ∷ []) (X4 ∷ []) tt tt Eq.refl

wp0799 : Complete 4 → ⟪ (CCZ012 ∷ CX12 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ []) ⟫ʷ
wp0799 c4 = pw3 c4 (CCZ012 ∷ CX12 ∷ Toff214 ∷ []) (CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0800 : Complete 4 → ⟪ (CZ01 ∷ CCZ134 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ01 ∷ []) ⟫ʷ
wp0800 c4 = pw2 c4 (CZ01 ∷ CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CZ01 ∷ []) tt tt Eq.refl

wp0801 : Complete 4 → ⟪ (CCZ014 ∷ CCZ134 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ014 ∷ []) ⟫ʷ
wp0801 c4 = pw2 c4 (CCZ014 ∷ CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0802 : Complete 4 → ⟪ (CZ01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) ⟫ʷ
wp0802 c4 = pw2 c4 (CZ01 ∷ CCZ014 ∷ []) (CZ01 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0803 : Complete 4 → ⟪ (CCZ012 ∷ CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff214 ∷ CCZ012 ∷ []) ⟫ʷ
wp0803 c4 = pw3 c4 (CCZ012 ∷ CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ []) (CX12 ∷ Toff214 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0804 : Complete 4 → ⟪ (CS02⁻ ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS02⁻ ∷ []) ⟫ʷ
wp0804 c4 = pw1 c4 (CS02⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0805 : Complete 4 → ⟪ (Toff023 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) ⟫ʷ
wp0805 c4 = pw1 c4 (Toff023 ∷ Toff324 ∷ []) (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0806 : Complete 4 → ⟪ (CCZ014 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) ⟫ʷ
wp0806 c4 = pw3 c4 (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0807 : Complete 4 → ⟪ (CCZ014 ∷ CX34 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ014 ∷ []) ⟫ʷ
wp0807 c4 = pw2 c4 (CCZ014 ∷ CX34 ∷ CCZ013 ∷ []) (CX34 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0808 : Complete 4 → ⟪ (CX34 ∷ CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ []) ⟫ʷ
wp0808 c4 = pw2 c4 (CX34 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX34 ∷ []) tt tt Eq.refl

wp0809 : Complete 4 → ⟪ (CX43 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX43 ∷ Toff024 ∷ []) ⟫ʷ
wp0809 c4 = pw1 c4 (CX43 ∷ Toff023 ∷ []) (Toff023 ∷ CX43 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0810 : Complete 4 → ⟪ (CCZ014 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ014 ∷ []) ⟫ʷ
wp0810 c4 = pw2 c4 (CCZ014 ∷ CX43 ∷ []) (CX43 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0811 : Complete 4 → ⟪ (CX43 ∷ Toff024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ []) ⟫ʷ
wp0811 c4 = pw1 c4 (CX43 ∷ Toff024 ∷ Toff024 ∷ []) (CX43 ∷ []) tt tt Eq.refl

wp0812 : Complete 4 → ⟪ (Sw34 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw34 ∷ []) ⟫ʷ
wp0812 c4 = pw1 c4 (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0813 : Complete 4 → ⟪ (Sw34 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Sw34 ∷ []) ⟫ʷ
wp0813 c4 = pw1 c4 (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0814 : Complete 4 → ⟪ (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ023 ∷ []) ⟫ʷ
wp0814 c4 = pw1 c4 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (Toff324 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0815 : Complete 4 → ⟪ (CCZ024 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0815 c4 = pw3 c4 (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0816 : Complete 4 → ⟪ (K3⁻ ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ K3⁻ ∷ []) ⟫ʷ
wp0816 c4 = pw2 c4 (K3⁻ ∷ Toff014 ∷ []) (Toff014 ∷ K3⁻ ∷ []) tt tt Eq.refl

wp0817 : Complete 4 → ⟪ (CS24 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS24 ∷ []) ⟫ʷ
wp0817 c4 = pw3 c4 (CS24 ∷ Toff014 ∷ []) (Toff014 ∷ CS24 ∷ []) tt tt Eq.refl

wp0818 : Complete 4 → ⟪ (CS34⁻ ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0818 c4 = pw2 c4 (CS34⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0819 : Complete 4 → ⟪ (K3 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ K3 ∷ []) ⟫ʷ
wp0819 c4 = pw2 c4 (K3 ∷ Toff014 ∷ []) (Toff014 ∷ K3 ∷ []) tt tt Eq.refl

wp0820 : Complete 4 → ⟪ (CCZ023 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wp0820 c4 = pw1 c4 (CCZ023 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0821 : Complete 4 → ⟪ (Toff324 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
wp0821 c4 = pw1 c4 (Toff324 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff324 ∷ []) tt tt Eq.refl

wp0822 : Complete 4 → ⟪ (CCZ124 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ124 ∷ []) ⟫ʷ
wp0822 c4 = pw3 c4 (CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0823 : Complete 4 → ⟪ (CS34⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0823 c4 = pw1 c4 (CS34⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0824 : Complete 4 → ⟪ (CCZ014 ∷ CX31 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) ⟫ʷ
wp0824 c4 = pw2 c4 (CCZ014 ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0825 : Complete 4 → ⟪ (CCZ034 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ
wp0825 c4 = pw2 c4 (CCZ034 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0826 : Complete 4 → ⟪ (CCZ024 ∷ Toff012 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ024 ∷ []) ⟫ʷ
wp0826 c4 = pw3 c4 (CCZ024 ∷ Toff012 ∷ CCZ124 ∷ []) (Toff012 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0827 : Complete 4 → ⟪ (CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ024 ∷ []) ⟫ʷ
wp0827 c4 = pw3 c4 (CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0828 : Complete 4 → ⟪ (CCZ013 ∷ Toff134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) ⟫ʷ
wp0828 c4 = pw2 c4 (CCZ013 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0829 : Complete 4 → ⟪ (CCZ013 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ []) ⟫ʷ
wp0829 c4 = pw2 c4 (CCZ013 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0830 : Complete 4 → ⟪ (CCZ013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ []) ⟫ʷ
wp0830 c4 = pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0831 : Complete 4 → ⟪ (CCZ034 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ034 ∷ []) ⟫ʷ
wp0831 c4 = pw2 c4 (CCZ034 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0832 : Complete 4 → ⟪ (Toff013 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) ⟫ʷ
wp0832 c4 = pw2 c4 (Toff013 ∷ Toff314 ∷ []) (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0833 : Complete 4 → ⟪ (CCZ024 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) ⟫ʷ
wp0833 c4 = pw3 c4 (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0834 : Complete 4 → ⟪ (CS03⁻ ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0834 c4 = pw2 c4 (CS03⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0835 : Complete 4 → ⟪ (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ014 ∷ []) ⟫ʷ
wp0835 c4 = pw2 c4 (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0836 : Complete 4 → ⟪ (Toff134 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ []) ⟫ʷ
wp0836 c4 = pw2 c4 (Toff134 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff134 ∷ []) tt tt Eq.refl

wp0837 : Complete 4 → ⟪ (CCZ023 ∷ CX23 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ []) ⟫ʷ
wp0837 c4 = pw1 c4 (CCZ023 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0838 : Complete 4 → ⟪ (CZ02 ∷ CCZ124 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CZ02 ∷ []) ⟫ʷ
wp0838 c4 = pw3 c4 (CZ02 ∷ CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CZ02 ∷ []) tt tt Eq.refl

wp0839 : Complete 4 → ⟪ (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ024 ∷ []) ⟫ʷ
wp0839 c4 = pw3 c4 (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0840 : Complete 4 → ⟪ (CZ02 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0840 c4 = pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CZ02 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0841 : Complete 4 → ⟪ (CCZ023 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff324 ∷ CCZ023 ∷ []) ⟫ʷ
wp0841 c4 = pw1 c4 (CCZ023 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ []) (CX23 ∷ Toff324 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0842 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) ⟫ʷ
wp0842 c4 = pw1 c4 (CCZ234 ∷ []) (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0843 : Complete 4 → ⟪ (Toff013 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) ⟫ʷ
wp0843 c4 = pw2 c4 (Toff013 ∷ Toff134 ∷ []) (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0844 : Complete 4 → ⟪ (CCZ024 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ234 ∷ CCZ024 ∷ []) ⟫ʷ
wp0844 c4 = pw1 c4 (CCZ024 ∷ CX30 ∷ []) (CX30 ∷ CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0845 : Complete 4 → ⟪ (CCZ024 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) ⟫ʷ
wp0845 c4 = pw1 c4 (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0846 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ234 ∷ CX30 ∷ []) ⟫ʷ
wp0846 c4 = pw1 c4 (CCZ234 ∷ []) (CX30 ∷ CCZ234 ∷ CX30 ∷ []) tt tt Eq.refl

wp0847 : Complete 4 → ⟪ (CS04 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CS04 ∷ []) ⟫ʷ
wp0847 c4 = pw1 c4 (CS04 ∷ S4 ∷ []) (S4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0848 : Complete 4 → ⟪ (CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CK40 ∷ []) ⟫ʷ
wp0848 c4 = pw1 c4 (CK40 ∷ S4 ∷ []) (S4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0849 : Complete 4 → ⟪ (S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S4 ∷ []) ⟫ʷ
wp0849 c4 = pw2 c4 (S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S4 ∷ []) tt tt Eq.refl

wp0850 : Complete 4 → ⟪ (CS04 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS04 ∷ []) ⟫ʷ
wp0850 c4 = pw2 c4 (CS04 ∷ CS14 ∷ []) (CS14 ∷ CS04 ∷ []) tt tt Eq.refl

wp0851 : Complete 4 → ⟪ (CS04 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS04 ∷ []) ⟫ʷ
wp0851 c4 = pw1 c4 (CS04 ∷ CS24 ∷ []) (CS24 ∷ CS04 ∷ []) tt tt Eq.refl

wp0852 : Complete 4 → ⟪ (CS04 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS04 ∷ []) ⟫ʷ
wp0852 c4 = pw1 c4 (CS04 ∷ CS34 ∷ []) (CS34 ∷ CS04 ∷ []) tt tt Eq.refl

wp0853 : Complete 4 → ⟪ (CK41 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK41 ∷ []) ⟫ʷ
wp0853 c4 = pw2 c4 (CK41 ∷ CS04 ∷ []) (CS04 ∷ CK41 ∷ []) tt tt Eq.refl

wp0854 : Complete 4 → ⟪ (CK42 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK42 ∷ []) ⟫ʷ
wp0854 c4 = pw1 c4 (CK42 ∷ CS04 ∷ []) (CS04 ∷ CK42 ∷ []) tt tt Eq.refl

wp0855 : Complete 4 → ⟪ (CK43 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK43 ∷ []) ⟫ʷ
wp0855 c4 = pw1 c4 (CK43 ∷ CS04 ∷ []) (CS04 ∷ CK43 ∷ []) tt tt Eq.refl

wp0856 : Complete 4 → ⟪ (CS04 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS04 ∷ []) ⟫ʷ
wp0856 c4 = pw2 c4 (CS04 ∷ CS13 ∷ []) (CS13 ∷ CS04 ∷ []) tt tt Eq.refl

wp0857 : Complete 4 → ⟪ (CS04 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS04 ∷ []) ⟫ʷ
wp0857 c4 = pw2 c4 (CS04 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04 ∷ []) tt tt Eq.refl

wp0858 : Complete 4 → ⟪ (CS04 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS04 ∷ []) ⟫ʷ
wp0858 c4 = pw2 c4 (CS04 ∷ Toff134 ∷ []) (Toff134 ∷ CS04 ∷ []) tt tt Eq.refl

wp0859 : Complete 4 → ⟪ (CS04 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS04 ∷ []) ⟫ʷ
wp0859 c4 = pw3 c4 (CS04 ∷ CS12 ∷ []) (CS12 ∷ CS04 ∷ []) tt tt Eq.refl

wp0860 : Complete 4 → ⟪ (CS04 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS04 ∷ []) ⟫ʷ
wp0860 c4 = pw3 c4 (CS04 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04 ∷ []) tt tt Eq.refl

wp0861 : Complete 4 → ⟪ (CK40 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK40 ∷ []) ⟫ʷ
wp0861 c4 = pw2 c4 (CK40 ∷ CS14 ∷ []) (CS14 ∷ CK40 ∷ []) tt tt Eq.refl

wp0862 : Complete 4 → ⟪ (CK40 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK40 ∷ []) ⟫ʷ
wp0862 c4 = pw1 c4 (CK40 ∷ CS24 ∷ []) (CS24 ∷ CK40 ∷ []) tt tt Eq.refl

wp0863 : Complete 4 → ⟪ (CS03 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS03 ∷ []) ⟫ʷ
wp0863 c4 = pw1 c4 (CS03 ∷ CS24 ∷ []) (CS24 ∷ CS03 ∷ []) tt tt Eq.refl

wp0864 : Complete 4 → ⟪ (CS03⁻ ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0864 c4 = pw1 c4 (CS03⁻ ∷ CS24 ∷ []) (CS24 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0865 : Complete 4 → ⟪ (CK40 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK40 ∷ []) ⟫ʷ
wp0865 c4 = pw1 c4 (CK40 ∷ CS34 ∷ []) (CS34 ∷ CK40 ∷ []) tt tt Eq.refl

wp0866 : Complete 4 → ⟪ (CS34 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS34 ∷ []) ⟫ʷ
wp0866 c4 = pw2 c4 (CS34 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS34 ∷ []) tt tt Eq.refl

wp0867 : Complete 4 → ⟪ (CK40 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK40 ∷ []) ⟫ʷ
wp0867 c4 = pw2 c4 (CK40 ∷ CK41 ∷ []) (CK41 ∷ CK40 ∷ []) tt tt Eq.refl

wp0868 : Complete 4 → ⟪ (CK40 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK40 ∷ []) ⟫ʷ
wp0868 c4 = pw1 c4 (CK40 ∷ CK42 ∷ []) (CK42 ∷ CK40 ∷ []) tt tt Eq.refl

wp0869 : Complete 4 → ⟪ (CK40 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK40 ∷ []) ⟫ʷ
wp0869 c4 = pw1 c4 (CK40 ∷ CK43 ∷ []) (CK43 ∷ CK40 ∷ []) tt tt Eq.refl

wp0870 : Complete 4 → ⟪ (CK40 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CK40 ∷ []) ⟫ʷ
wp0870 c4 = pw1 c4 (CK40 ∷ Toff324 ∷ []) (Toff324 ∷ CK40 ∷ []) tt tt Eq.refl

wp0871 : Complete 4 → ⟪ (CK40 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CK40 ∷ []) ⟫ʷ
wp0871 c4 = pw2 c4 (CK40 ∷ CS13 ∷ []) (CS13 ∷ CK40 ∷ []) tt tt Eq.refl

wp0872 : Complete 4 → ⟪ (CK40 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CK40 ∷ []) ⟫ʷ
wp0872 c4 = pw2 c4 (CK40 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CK40 ∷ []) tt tt Eq.refl

wp0873 : Complete 4 → ⟪ (CK40 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CK40 ∷ []) ⟫ʷ
wp0873 c4 = pw2 c4 (CK40 ∷ Toff134 ∷ []) (Toff134 ∷ CK40 ∷ []) tt tt Eq.refl

wp0874 : Complete 4 → ⟪ (CK40 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CK40 ∷ []) ⟫ʷ
wp0874 c4 = pw3 c4 (CK40 ∷ CS12 ∷ []) (CS12 ∷ CK40 ∷ []) tt tt Eq.refl

wp0875 : Complete 4 → ⟪ (CK40 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CK40 ∷ []) ⟫ʷ
wp0875 c4 = pw3 c4 (CK40 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK40 ∷ []) tt tt Eq.refl

wp0876 : Complete 4 → ⟪ (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ014 ∷ []) ⟫ʷ
wp0876 c4 = pw2 c4 (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) (CK41 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0877 : Complete 4 → ⟪ (CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CK41 ∷ []) ⟫ʷ
wp0877 c4 = pw2 c4 (CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ []) (CZ01 ∷ CK41 ∷ []) tt tt Eq.refl

wp0878 : Complete 4 → ⟪ (CK42 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CK42 ∷ []) ⟫ʷ
wp0878 c4 = pw1 c4 (CK42 ∷ CS03 ∷ []) (CS03 ∷ CK42 ∷ []) tt tt Eq.refl

wp0879 : Complete 4 → ⟪ (CK42 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CK42 ∷ []) ⟫ʷ
wp0879 c4 = pw1 c4 (CK42 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CK42 ∷ []) tt tt Eq.refl

wp0880 : Complete 4 → ⟪ (CCZ013 ∷ CK43 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK43 ∷ []) ⟫ʷ
wp0880 c4 = pw2 c4 (CCZ013 ∷ CK43 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK43 ∷ []) tt tt Eq.refl

wp0881 : Complete 4 → ⟪ (CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CCZ034 ∷ []) ⟫ʷ
wp0881 c4 = pw1 c4 (CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ []) (CK43 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0882 : Complete 4 → ⟪ (CZ03 ∷ CK43 ∷ CZ03 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CK43 ∷ []) ⟫ʷ
wp0882 c4 = pw1 c4 (CZ03 ∷ CK43 ∷ CZ03 ∷ CZ03 ∷ []) (CZ03 ∷ CK43 ∷ []) tt tt Eq.refl

wp0883 : Complete 4 → ⟪ (CCZ034 ∷ CCZ014 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ034 ∷ []) ⟫ʷ
wp0883 c4 = pw2 c4 (CCZ034 ∷ CCZ014 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0884 : Complete 4 → ⟪ (CCZ034 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ034 ∷ Toff301 ∷ []) ⟫ʷ
wp0884 c4 = pw2 c4 (CCZ034 ∷ CCZ014 ∷ []) (Toff301 ∷ CCZ034 ∷ Toff301 ∷ []) tt tt Eq.refl

wp0885 : Complete 4 → ⟪ (CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0885 c4 = pw2 c4 (CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0886 : Complete 4 → ⟪ (CZ01 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CZ01 ∷ CCZ124 ∷ []) ⟫ʷ
wp0886 c4 = pw3 c4 (CZ01 ∷ Toff024 ∷ []) (Toff024 ∷ CZ01 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0887 : Complete 4 → ⟪ (Toff024 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff024 ∷ []) ⟫ʷ
wp0887 c4 = pw1 c4 (Toff024 ∷ X3 ∷ []) (X3 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0888 : Complete 4 → ⟪ (CCZ034 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ
wp0888 c4 = pw1 c4 (CCZ034 ∷ K4 ∷ []) (K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0889 : Complete 4 → ⟪ (CCZ034 ∷ CK34 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ CK34 ∷ CZ04 ∷ CCZ034 ∷ []) ⟫ʷ
wp0889 c4 = pw1 c4 (CCZ034 ∷ CK34 ∷ []) (CZ04 ∷ CK34 ∷ CZ04 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0890 : Complete 4 → ⟪ (CCZ034 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CCZ034 ∷ []) ⟫ʷ
wp0890 c4 = pw1 c4 (CCZ034 ∷ S3 ∷ []) (S3 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0891 : Complete 4 → ⟪ (K4 ∷ CK34 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ S3 ∷ []) ⟫ʷ
wp0891 c4 = pw1 c4 (K4 ∷ CK34 ∷ S3 ∷ []) (K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ S3 ∷ []) tt tt Eq.refl

wp0892 : Complete 4 → ⟪ (K4 ∷ CK34 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ ι ∷ []) ⟫ʷ
wp0892 c4 = pw1 c4 (K4 ∷ CK34 ∷ ι ∷ []) (K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ ι ∷ []) tt tt Eq.refl

wp0893 : Complete 4 → ⟪ (CCZ124 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ ι1 ∷ CCZ124 ∷ []) ⟫ʷ
wp0893 c4 = pw0 c4 (CCZ124 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ X3 ∷ []) (X3 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ ι1 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0894 : Complete 4 → ⟪ (Toff402 ∷ CS14 ∷ Toff402 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0894 c4 = pw3 c4 (Toff402 ∷ CS14 ∷ Toff402 ∷ CS14⁻ ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0895 : Complete 4 → ⟪ (CCZ134 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ134 ∷ CCZ014 ∷ []) ⟫ʷ
wp0895 c4 = pw2 c4 (CCZ134 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ134 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0896 : Complete 4 → ⟪ (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ234 ∷ []) ⟫ʷ
wp0896 c4 = pw1 c4 (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (Toff302 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0897 : Complete 4 → ⟪ (CS04 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS04 ∷ []) ⟫ʷ
wp0897 c4 = pw2 c4 (CS04 ∷ Toff301 ∷ []) (Toff301 ∷ CS04 ∷ []) tt tt Eq.refl

wp0898 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ024 ∷ CX21 ∷ []) ⟫ʷ
wp0898 c4 = pw3 c4 (CCZ024 ∷ []) (CX21 ∷ CCZ024 ∷ CX21 ∷ []) tt tt Eq.refl

wp0899 : Complete 4 → ⟪ (CCZ014 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) ⟫ʷ
wp0899 c4 = pw3 c4 (CCZ014 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0900 : Complete 4 → ⟪ (CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp0900 c4 = pw3 c4 (CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp0901 : Complete 4 → ⟪ (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0901 c4 = pw3 c4 (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0902 : Complete 4 → ⟪ (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0902 c4 = pw1 c4 (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) [] tt tt Eq.refl

wp0903 : Complete 4 → ⟪ (CK40 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wp0903 c4 = pw1 c4 (CK40 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wp0904 : Complete 4 → ⟪ (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wp0904 c4 = pw1 c4 (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wp0905 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0905 c4 = pw2 c4 (CCZ014 ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0906 : Complete 4 → ⟪ (CCZ024 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ024 ∷ []) ⟫ʷ
wp0906 c4 = pw1 c4 (CCZ024 ∷ CS04 ∷ []) (CS04 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0907 : Complete 4 → ⟪ (CS04 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ []) ⟫ʷ
wp0907 c4 = pw2 c4 (CS04 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ []) tt tt Eq.refl

wp0908 : Complete 4 → ⟪ (CCZ014 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ014 ∷ []) ⟫ʷ
wp0908 c4 = pw2 c4 (CCZ014 ∷ CS14 ∷ []) (CS14 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0909 : Complete 4 → ⟪ (CCZ024 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ024 ∷ []) ⟫ʷ
wp0909 c4 = pw1 c4 (CCZ024 ∷ CS24 ∷ []) (CS24 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0910 : Complete 4 → ⟪ (CS14 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ []) ⟫ʷ
wp0910 c4 = pw2 c4 (CS14 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ []) tt tt Eq.refl

wp0911 : Complete 4 → ⟪ (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ024 ∷ []) ⟫ʷ
wp0911 c4 = pw1 c4 (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (CX34 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0912 : Complete 4 → ⟪ (CX34 ∷ CCZ023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ []) ⟫ʷ
wp0912 c4 = pw1 c4 (CX34 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX34 ∷ []) tt tt Eq.refl

wp0913 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ013 ∷ CX34 ∷ []) ⟫ʷ
wp0913 c4 = pw2 c4 (CCZ013 ∷ []) (CX34 ∷ CCZ013 ∷ CX34 ∷ []) tt tt Eq.refl

wp0914 : Complete 4 → ⟪ (CCZ024 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ024 ∷ []) ⟫ʷ
wp0914 c4 = pw1 c4 (CCZ024 ∷ CX43 ∷ []) (CX43 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0915 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ014 ∷ CX43 ∷ []) ⟫ʷ
wp0915 c4 = pw2 c4 (CCZ014 ∷ []) (CX43 ∷ CCZ014 ∷ CX43 ∷ []) tt tt Eq.refl

wp0916 : Complete 4 → ⟪ (CCZ013 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) ⟫ʷ
wp0916 c4 = pw2 c4 (CCZ013 ∷ CX43 ∷ []) (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0917 : Complete 4 → ⟪ (CCZ014 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) ⟫ʷ
wp0917 c4 = pw2 c4 (CCZ014 ∷ CX34 ∷ []) (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0918 : Complete 4 → ⟪ (CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
wp0918 c4 = pw2 c4 (CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl

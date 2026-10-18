------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP06 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp1123 : Complete 4 → ⟪ (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ []) ⟫ʷ
wp1123 c4 = pw3 c4 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ []) (CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1124 : Complete 4 → ⟪ (CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wp1124 c4 = pw3 c4 (CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ []) (S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1125 : Complete 4 → ⟪ (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) ⟫ʷ
wp1125 c4 = pw3 c4 (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) tt tt Eq.refl

wp1126 : Complete 4 → ⟪ (CK34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CK34 ∷ []) ⟫ʷ
wp1126 c4 = pw1 c4 (CK34 ∷ CCZ034 ∷ []) (Toff403 ∷ CK34 ∷ []) tt tt Eq.refl

wp1127 : Complete 4 → ⟪ (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ []) ⟫ʷ
wp1127 c4 = pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl

wp1128 : Complete 4 → ⟪ (CCZ234 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ234 ∷ CCZ024 ∷ []) ⟫ʷ
wp1128 c4 = pw1 c4 (CCZ234 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1129 : Complete 4 → ⟪ (CCZ134 ∷ Toff301 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ134 ∷ []) ⟫ʷ
wp1129 c4 = pw2 c4 (CCZ134 ∷ Toff301 ∷ CCZ014 ∷ []) (Toff301 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1130 : Complete 4 → ⟪ (CCZ034 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CCZ034 ∷ []) ⟫ʷ
wp1130 c4 = pw2 c4 (CCZ034 ∷ K1 ∷ []) (K1 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1131 : Complete 4 → ⟪ (CCZ034 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp1131 c4 = pw2 c4 (CCZ034 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1132 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ []) ⟫ʷ
wp1132 c4 = pw2 c4 (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1⁻ ∷ []) (Toff104 ∷ []) tt tt Eq.refl

wp1133 : Complete 4 → ⟪ (CCZ134 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ
wp1133 c4 = pw2 c4 (CCZ134 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1134 : Complete 4 → ⟪ (CCZ024 ∷ CCZ034 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ034 ∷ []) ⟫ʷ
wp1134 c4 = pw1 c4 (CCZ024 ∷ CCZ034 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1135 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ024 ∷ CCZ034 ∷ []) ⟫ʷ
wp1135 c4 = pw1 c4 (CCZ024 ∷ []) (CCZ034 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1136 : Complete 4 → ⟪ (CCZ024 ∷ CCZ234 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ234 ∷ []) ⟫ʷ
wp1136 c4 = pw1 c4 (CCZ024 ∷ CCZ234 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1137 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ024 ∷ CCZ234 ∷ []) ⟫ʷ
wp1137 c4 = pw1 c4 (CCZ024 ∷ []) (CCZ234 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1138 : Complete 4 → ⟪ (CCZ024 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ024 ∷ []) ⟫ʷ
wp1138 c4 = pw1 c4 (CCZ024 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1139 : Complete 4 → ⟪ (CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ []) ⟫ʷ
wp1139 c4 = pw3 c4 (CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ []) (CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1140 : Complete 4 → ⟪ (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp1140 c4 = pw3 c4 (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) [] tt tt Eq.refl

wp1141 : Complete 4 → ⟪ (CX02 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX02 ∷ Toff304 ∷ []) ⟫ʷ
wp1141 c4 = pw1 c4 (CX02 ∷ Toff324 ∷ []) (Toff324 ∷ CX02 ∷ Toff304 ∷ []) tt tt Eq.refl

wp1142 : Complete 4 → ⟪ (CCZ013 ∷ Toff304 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ013 ∷ []) ⟫ʷ
wp1142 c4 = pw2 c4 (CCZ013 ∷ Toff304 ∷ CCZ014 ∷ []) (Toff304 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1143 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) ⟫ʷ
wp1143 c4 = pw2 c4 (CCZ014 ∷ []) (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) tt tt Eq.refl

wp1144 : Complete 4 → ⟪ (Toff304 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff304 ∷ []) ⟫ʷ
wp1144 c4 = pw1 c4 (Toff304 ∷ Toff324 ∷ []) (Toff324 ∷ Toff304 ∷ []) tt tt Eq.refl

wp1145 : Complete 4 → ⟪ (CX02 ∷ Toff304 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
wp1145 c4 = pw1 c4 (CX02 ∷ Toff304 ∷ Toff304 ∷ []) (CX02 ∷ []) tt tt Eq.refl

wp1146 : Complete 4 → ⟪ (CCZ034 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Sw02 ∷ CCZ234 ∷ []) ⟫ʷ
wp1146 c4 = pw1 c4 (CCZ034 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1147 : Complete 4 → ⟪ (Sw02 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw02 ∷ []) ⟫ʷ
wp1147 c4 = pw1 c4 (Sw02 ∷ Toff324 ∷ []) (Toff304 ∷ Sw02 ∷ []) tt tt Eq.refl

wp1148 : Complete 4 → ⟪ (CCZ234 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Sw02 ∷ CCZ034 ∷ []) ⟫ʷ
wp1148 c4 = pw1 c4 (CCZ234 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1149 : Complete 4 → ⟪ (Sw02 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sw02 ∷ []) ⟫ʷ
wp1149 c4 = pw1 c4 (Sw02 ∷ Toff403 ∷ []) (Toff423 ∷ Sw02 ∷ []) tt tt Eq.refl

wp1150 : Complete 4 → ⟪ (CCZ012 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ012 ∷ CCZ014 ∷ []) ⟫ʷ
wp1150 c4 = pw3 c4 (CCZ012 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1151 : Complete 4 → ⟪ (CX30 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX30 ∷ Toff234 ∷ []) ⟫ʷ
wp1151 c4 = pw1 c4 (CX30 ∷ Toff204 ∷ []) (Toff204 ∷ CX30 ∷ Toff234 ∷ []) tt tt Eq.refl

wp1152 : Complete 4 → ⟪ (CS14 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS14 ∷ []) ⟫ʷ
wp1152 c4 = pw3 c4 (CS14 ∷ Toff204 ∷ []) (Toff204 ∷ CS14 ∷ []) tt tt Eq.refl

wp1153 : Complete 4 → ⟪ (Toff204 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff204 ∷ []) ⟫ʷ
wp1153 c4 = pw1 c4 (Toff204 ∷ Toff234 ∷ []) (Toff234 ∷ Toff204 ∷ []) tt tt Eq.refl

wp1154 : Complete 4 → ⟪ (CX30 ∷ Toff234 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
wp1154 c4 = pw1 c4 (CX30 ∷ Toff234 ∷ Toff234 ∷ []) (CX30 ∷ []) tt tt Eq.refl

wp1155 : Complete 4 → ⟪ (CCZ234 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw03 ∷ CCZ024 ∷ []) ⟫ʷ
wp1155 c4 = pw1 c4 (CCZ234 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1156 : Complete 4 → ⟪ (Sw03 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Sw03 ∷ []) ⟫ʷ
wp1156 c4 = pw1 c4 (Sw03 ∷ Toff204 ∷ []) (Toff234 ∷ Sw03 ∷ []) tt tt Eq.refl

wp1157 : Complete 4 → ⟪ (CCZ024 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw03 ∷ CCZ234 ∷ []) ⟫ʷ
wp1157 c4 = pw1 c4 (CCZ024 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1158 : Complete 4 → ⟪ (Sw03 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw03 ∷ []) ⟫ʷ
wp1158 c4 = pw1 c4 (Sw03 ∷ Toff423 ∷ []) (Toff402 ∷ Sw03 ∷ []) tt tt Eq.refl

wp1159 : Complete 4 → ⟪ (CCZ013 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ013 ∷ CCZ014 ∷ []) ⟫ʷ
wp1159 c4 = pw2 c4 (CCZ013 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ013 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1160 : Complete 4 → ⟪ (CX20 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX20 ∷ Toff324 ∷ []) ⟫ʷ
wp1160 c4 = pw1 c4 (CX20 ∷ Toff304 ∷ []) (Toff304 ∷ CX20 ∷ Toff324 ∷ []) tt tt Eq.refl

wp1161 : Complete 4 → ⟪ (CX20 ∷ Toff324 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
wp1161 c4 = pw1 c4 (CX20 ∷ Toff324 ∷ Toff324 ∷ []) (CX20 ∷ []) tt tt Eq.refl

wp1162 : Complete 4 → ⟪ (Sw02 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sw02 ∷ []) ⟫ʷ
wp1162 c4 = pw1 c4 (Sw02 ∷ Toff304 ∷ []) (Toff324 ∷ Sw02 ∷ []) tt tt Eq.refl

wp1163 : Complete 4 → ⟪ (Sw02 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw02 ∷ []) ⟫ʷ
wp1163 c4 = pw1 c4 (Sw02 ∷ Toff423 ∷ []) (Toff403 ∷ Sw02 ∷ []) tt tt Eq.refl

wp1164 : Complete 4 → ⟪ (CX14 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CX14 ∷ []) ⟫ʷ
wp1164 c4 = pw3 c4 (CX14 ∷ Toff201 ∷ []) (Toff201 ∷ CX14 ∷ []) tt tt Eq.refl

wp1165 : Complete 4 → ⟪ (CX41 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CX41 ∷ Toff204 ∷ []) ⟫ʷ
wp1165 c4 = pw3 c4 (CX41 ∷ Toff201 ∷ []) (Toff201 ∷ CX41 ∷ Toff204 ∷ []) tt tt Eq.refl

wp1166 : Complete 4 → ⟪ (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ234 ∷ []) ⟫ʷ
wp1166 c4 = pw1 c4 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (Toff204 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1167 : Complete 4 → ⟪ (CX04 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CX04 ∷ []) ⟫ʷ
wp1167 c4 = pw3 c4 (CX04 ∷ Toff201 ∷ []) (Toff201 ∷ CX04 ∷ []) tt tt Eq.refl

wp1168 : Complete 4 → ⟪ (CX41 ∷ Toff204 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wp1168 c4 = pw3 c4 (CX41 ∷ Toff204 ∷ Toff204 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wp1169 : Complete 4 → ⟪ (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ []) ⟫ʷ
wp1169 c4 = pw1 c4 (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (Toff204 ∷ []) tt tt Eq.refl

wp1170 : Complete 4 → ⟪ (CS04⁻ ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS04⁻ ∷ []) ⟫ʷ
wp1170 c4 = pw2 c4 (CS04⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp1171 : Complete 4 → ⟪ (CCZ234 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ CCZ234 ∷ []) ⟫ʷ
wp1171 c4 = pw1 c4 (CCZ234 ∷ CX40 ∷ []) (CX40 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1172 : Complete 4 → ⟪ (Toff204 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ []) ⟫ʷ
wp1172 c4 = pw1 c4 (Toff204 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff204 ∷ []) tt tt Eq.refl

wp1173 : Complete 4 → ⟪ (CCZ014 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ014 ∷ []) ⟫ʷ
wp1173 c4 = pw2 c4 (CCZ014 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1174 : Complete 4 → ⟪ (CCZ014 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ014 ∷ []) ⟫ʷ
wp1174 c4 = pw3 c4 (CCZ014 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1175 : Complete 4 → ⟪ (CX30 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CX30 ∷ []) ⟫ʷ
wp1175 c4 = pw1 c4 (CX30 ∷ Toff234 ∷ []) (Toff234 ∷ CX30 ∷ []) tt tt Eq.refl

wp1176 : Complete 4 → ⟪ (CX03 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CX03 ∷ Toff204 ∷ []) ⟫ʷ
wp1176 c4 = pw1 c4 (CX03 ∷ Toff234 ∷ []) (Toff234 ∷ CX03 ∷ Toff204 ∷ []) tt tt Eq.refl

wp1177 : Complete 4 → ⟪ (CCZ012 ∷ Toff204 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ012 ∷ []) ⟫ʷ
wp1177 c4 = pw3 c4 (CCZ012 ∷ Toff204 ∷ CCZ014 ∷ []) (Toff204 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1178 : Complete 4 → ⟪ (CX40 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CX40 ∷ []) ⟫ʷ
wp1178 c4 = pw1 c4 (CX40 ∷ Toff234 ∷ []) (Toff234 ∷ CX40 ∷ []) tt tt Eq.refl

wp1179 : Complete 4 → ⟪ (CX03 ∷ Toff204 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
wp1179 c4 = pw1 c4 (CX03 ∷ Toff204 ∷ Toff204 ∷ []) (CX03 ∷ []) tt tt Eq.refl

wp1180 : Complete 4 → ⟪ (Sw03 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw03 ∷ []) ⟫ʷ
wp1180 c4 = pw1 c4 (Sw03 ∷ Toff234 ∷ []) (Toff204 ∷ Sw03 ∷ []) tt tt Eq.refl

wp1181 : Complete 4 → ⟪ (Sw03 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sw03 ∷ []) ⟫ʷ
wp1181 c4 = pw1 c4 (Sw03 ∷ Toff402 ∷ []) (Toff423 ∷ Sw03 ∷ []) tt tt Eq.refl

wp1182 : Complete 4 → ⟪ (Toff234 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff204 ∷ Toff234 ∷ []) ⟫ʷ
wp1182 c4 = pw1 c4 (Toff234 ∷ Toff304 ∷ []) (Toff304 ∷ Toff204 ∷ Toff234 ∷ []) tt tt Eq.refl

wp1183 : Complete 4 → ⟪ (CS14⁻ ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS14⁻ ∷ []) ⟫ʷ
wp1183 c4 = pw3 c4 (CS14⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp1184 : Complete 4 → ⟪ (Toff204 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff204 ∷ []) ⟫ʷ
wp1184 c4 = pw1 c4 (Toff204 ∷ Toff304 ∷ []) (Toff304 ∷ Toff204 ∷ []) tt tt Eq.refl

wp1185 : Complete 4 → ⟪ (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ []) ⟫ʷ
wp1185 c4 = pw1 c4 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl

wp1186 : Complete 4 → ⟪ (CS04⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS04⁻ ∷ []) ⟫ʷ
wp1186 c4 = pw3 c4 (CS04⁻ ∷ Toff201 ∷ []) (Toff201 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp1187 : Complete 4 → ⟪ (CS04 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS04 ∷ []) ⟫ʷ
wp1187 c4 = pw3 c4 (CS04 ∷ Toff201 ∷ []) (Toff201 ∷ CS04 ∷ []) tt tt Eq.refl

wp1188 : Complete 4 → ⟪ (Toff304 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ []) ⟫ʷ
wp1188 c4 = pw1 c4 (Toff304 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff304 ∷ []) tt tt Eq.refl

wp1189 : Complete 4 → ⟪ (CCZ014 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ014 ∷ []) ⟫ʷ
wp1189 c4 = pw3 c4 (CCZ014 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1190 : Complete 4 → ⟪ (CCZ024 ∷ CX10 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ024 ∷ []) ⟫ʷ
wp1190 c4 = pw3 c4 (CCZ024 ∷ CX10 ∷ CCZ124 ∷ []) (CX10 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1191 : Complete 4 → ⟪ (CX10 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wp1191 c4 = pw3 c4 (CX10 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX10 ∷ []) tt tt Eq.refl

wp1192 : Complete 4 → ⟪ (CCZ024 ∷ Toff203 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ024 ∷ []) ⟫ʷ
wp1192 c4 = pw1 c4 (CCZ024 ∷ Toff203 ∷ CCZ034 ∷ []) (Toff203 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1193 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) ⟫ʷ
wp1193 c4 = pw1 c4 (CCZ034 ∷ []) (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) tt tt Eq.refl

wp1194 : Complete 4 → ⟪ (CCZ012 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ012 ∷ CCZ014 ∷ []) ⟫ʷ
wp1194 c4 = pw3 c4 (CCZ012 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1195 : Complete 4 → ⟪ (CS01⁻ ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS01⁻ ∷ []) ⟫ʷ
wp1195 c4 = pw3 c4 (CS01⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp1196 : Complete 4 → ⟪ (CCZ124 ∷ CX01 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ124 ∷ []) ⟫ʷ
wp1196 c4 = pw3 c4 (CCZ124 ∷ CX01 ∷ CCZ024 ∷ []) (CX01 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1197 : Complete 4 → ⟪ (CCZ024 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ024 ∷ CCZ034 ∷ []) ⟫ʷ
wp1197 c4 = pw1 c4 (CCZ024 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1198 : Complete 4 → ⟪ (CX01 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
wp1198 c4 = pw3 c4 (CX01 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX01 ∷ []) tt tt Eq.refl

wp1199 : Complete 4 → ⟪ (CS34 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS34 ∷ []) ⟫ʷ
wp1199 c4 = pw1 c4 (CS34 ∷ Toff203 ∷ []) (Toff203 ∷ CS34 ∷ []) tt tt Eq.refl

wp1200 : Complete 4 → ⟪ (Toff204 ∷ Toff304 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff204 ∷ []) ⟫ʷ
wp1200 c4 = pw1 c4 (Toff204 ∷ Toff304 ∷ Toff324 ∷ []) (Toff324 ∷ Toff204 ∷ []) tt tt Eq.refl

wp1201 : Complete 4 → ⟪ (CS14⁻ ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS14⁻ ∷ []) ⟫ʷ
wp1201 c4 = pw2 c4 (CS14⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp1202 : Complete 4 → ⟪ (CCZ034 ∷ Toff302 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ034 ∷ []) ⟫ʷ
wp1202 c4 = pw1 c4 (CCZ034 ∷ Toff302 ∷ CCZ024 ∷ []) (Toff302 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1203 : Complete 4 → ⟪ (CS01⁻ ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS01⁻ ∷ []) ⟫ʷ
wp1203 c4 = pw2 c4 (CS01⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp1204 : Complete 4 → ⟪ (CCZ134 ∷ CX01 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ134 ∷ []) ⟫ʷ
wp1204 c4 = pw2 c4 (CCZ134 ∷ CX01 ∷ CCZ034 ∷ []) (CX01 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1205 : Complete 4 → ⟪ (CCZ034 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ
wp1205 c4 = pw1 c4 (CCZ034 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1206 : Complete 4 → ⟪ (CCZ134 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ CCZ134 ∷ []) ⟫ʷ
wp1206 c4 = pw2 c4 (CCZ134 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1207 : Complete 4 → ⟪ (CX01 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
wp1207 c4 = pw2 c4 (CX01 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX01 ∷ []) tt tt Eq.refl

wp1208 : Complete 4 → ⟪ (Toff023 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff234 ∷ Toff023 ∷ []) ⟫ʷ
wp1208 c4 = pw1 c4 (Toff023 ∷ Toff234 ∷ []) (Toff034 ∷ Toff234 ∷ Toff023 ∷ []) tt tt Eq.refl

wp1209 : Complete 4 → ⟪ (CCZ014 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ134 ∷ CCZ014 ∷ []) ⟫ʷ
wp1209 c4 = pw2 c4 (CCZ014 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1210 : Complete 4 → ⟪ (CCZ014 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CCZ014 ∷ []) ⟫ʷ
wp1210 c4 = pw3 c4 (CCZ014 ∷ K2 ∷ []) (K2 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1211 : Complete 4 → ⟪ (CCZ014 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp1211 c4 = pw3 c4 (CCZ014 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1212 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ134 ∷ Toff034 ∷ []) ⟫ʷ
wp1212 c4 = pw2 c4 (CCZ134 ∷ []) (Toff034 ∷ CCZ134 ∷ Toff034 ∷ []) tt tt Eq.refl

wp1213 : Complete 4 → ⟪ (CCZ014 ∷ CCZ134 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ014 ∷ []) ⟫ʷ
wp1213 c4 = pw2 c4 (CCZ014 ∷ CCZ134 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1214 : Complete 4 → ⟪ (CCZ034 ∷ CCZ134 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ034 ∷ []) ⟫ʷ
wp1214 c4 = pw2 c4 (CCZ034 ∷ CCZ134 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1215 : Complete 4 → ⟪ (Toff234 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ []) ⟫ʷ
wp1215 c4 = pw1 c4 (Toff234 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff234 ∷ []) tt tt Eq.refl

wp1216 : Complete 4 → ⟪ (CK40 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CK40 ∷ []) ⟫ʷ
wp1216 c4 = pw1 c4 (CK40 ∷ CCZ034 ∷ []) (Toff034 ∷ CK40 ∷ []) tt tt Eq.refl

wp1217 : Complete 4 → ⟪ (CK40 ∷ CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp1217 c4 = pw1 c4 (CK40 ∷ CK40⁻ ∷ []) [] tt tt Eq.refl

wp1218 : Complete 4 → ⟪ (CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK40⁻ ∷ []) ⟫ʷ
wp1218 c4 = pw1 c4 (CK40 ∷ S4 ∷ []) (CK40⁻ ∷ []) tt tt Eq.refl

wp1219 : Complete 4 → ⟪ (CCZ234 ∷ CCZ034 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ234 ∷ []) ⟫ʷ
wp1219 c4 = pw1 c4 (CCZ234 ∷ CCZ034 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1220 : Complete 4 → ⟪ (K3⁻ ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ K3⁻ ∷ []) ⟫ʷ
wp1220 c4 = pw1 c4 (K3⁻ ∷ Toff204 ∷ []) (Toff204 ∷ K3⁻ ∷ []) tt tt Eq.refl

wp1221 : Complete 4 → ⟪ (CS01⁻ ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS01⁻ ∷ []) ⟫ʷ
wp1221 c4 = pw3 c4 (CS01⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp1222 : Complete 4 → ⟪ (K3 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ K3 ∷ []) ⟫ʷ
wp1222 c4 = pw1 c4 (K3 ∷ Toff204 ∷ []) (Toff204 ∷ K3 ∷ []) tt tt Eq.refl

wp1223 : Complete 4 → ⟪ (CCZ124 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ124 ∷ CCZ014 ∷ []) ⟫ʷ
wp1223 c4 = pw3 c4 (CCZ124 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1224 : Complete 4 → ⟪ (CS14⁻ ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS14⁻ ∷ []) ⟫ʷ
wp1224 c4 = pw2 c4 (CS14⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp1225 : Complete 4 → ⟪ (CS01⁻ ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS01⁻ ∷ []) ⟫ʷ
wp1225 c4 = pw2 c4 (CS01⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp1226 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ014 ∷ CX13 ∷ []) ⟫ʷ
wp1226 c4 = pw2 c4 (CCZ014 ∷ []) (CX13 ∷ CCZ014 ∷ CX13 ∷ []) tt tt Eq.refl

wp1227 : Complete 4 → ⟪ (CCZ234 ∷ Toff203 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ234 ∷ []) ⟫ʷ
wp1227 c4 = pw1 c4 (CCZ234 ∷ Toff203 ∷ CCZ034 ∷ []) (Toff203 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1228 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ034 ∷ CX31 ∷ []) ⟫ʷ
wp1228 c4 = pw2 c4 (CCZ034 ∷ []) (CX31 ∷ CCZ034 ∷ CX31 ∷ []) tt tt Eq.refl

wp1229 : Complete 4 → ⟪ (CCZ014 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ034 ∷ CCZ014 ∷ []) ⟫ʷ
wp1229 c4 = pw2 c4 (CCZ014 ∷ CX31 ∷ []) (CX31 ∷ CCZ034 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1230 : Complete 4 → ⟪ (CCZ034 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ014 ∷ CCZ034 ∷ []) ⟫ʷ
wp1230 c4 = pw2 c4 (CCZ034 ∷ CX13 ∷ []) (CX13 ∷ CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1231 : Complete 4 → ⟪ (CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp1231 c4 = pw2 c4 (CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp1232 : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wp1232 c4 = pw3 c4 (CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wp1233 : Complete 4 → ⟪ (CCZ012 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ012 ∷ CCZ124 ∷ []) ⟫ʷ
wp1233 c4 = pw3 c4 (CCZ012 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ012 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1234 : Complete 4 → ⟪ (CX31 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX31 ∷ Toff034 ∷ []) ⟫ʷ
wp1234 c4 = pw2 c4 (CX31 ∷ Toff014 ∷ []) (Toff014 ∷ CX31 ∷ Toff034 ∷ []) tt tt Eq.refl

wp1235 : Complete 4 → ⟪ (CCZ023 ∷ Toff034 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ023 ∷ []) ⟫ʷ
wp1235 c4 = pw1 c4 (CCZ023 ∷ Toff034 ∷ CCZ234 ∷ []) (Toff034 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1236 : Complete 4 → ⟪ (CX31 ∷ Toff034 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
wp1236 c4 = pw2 c4 (CX31 ∷ Toff034 ∷ Toff034 ∷ []) (CX31 ∷ []) tt tt Eq.refl

wp1237 : Complete 4 → ⟪ (Sw13 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw13 ∷ []) ⟫ʷ
wp1237 c4 = pw2 c4 (Sw13 ∷ Toff014 ∷ []) (Toff034 ∷ Sw13 ∷ []) tt tt Eq.refl

wp1238 : Complete 4 → ⟪ (Sw13 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw13 ∷ []) ⟫ʷ
wp1238 c4 = pw2 c4 (Sw13 ∷ Toff403 ∷ []) (Toff401 ∷ Sw13 ∷ []) tt tt Eq.refl

wp1239 : Complete 4 → ⟪ (K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ []) ⟫ʷ
wp1239 c4 = pw2 c4 (K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ []) (Toff014 ∷ []) tt tt Eq.refl

wp1240 : Complete 4 → ⟪ (Toff014 ∷ CCZ134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ []) ⟫ʷ
wp1240 c4 = pw2 c4 (Toff014 ∷ CCZ134 ∷ CCZ134 ∷ []) (Toff014 ∷ []) tt tt Eq.refl

wp1241 : Complete 4 → ⟪ (Toff034 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff014 ∷ Toff034 ∷ []) ⟫ʷ
wp1241 c4 = pw2 c4 (Toff034 ∷ Toff314 ∷ []) (Toff314 ∷ Toff014 ∷ Toff034 ∷ []) tt tt Eq.refl

wp1242 : Complete 4 → ⟪ (CCZ023 ∷ CCZ234 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ023 ∷ []) ⟫ʷ
wp1242 c4 = pw1 c4 (CCZ023 ∷ CCZ234 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1243 : Complete 4 → ⟪ (CCZ023 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ023 ∷ Toff034 ∷ []) ⟫ʷ
wp1243 c4 = pw1 c4 (CCZ023 ∷ CCZ234 ∷ []) (Toff034 ∷ CCZ023 ∷ Toff034 ∷ []) tt tt Eq.refl

wp1244 : Complete 4 → ⟪ (CS24⁻ ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS24⁻ ∷ []) ⟫ʷ
wp1244 c4 = pw3 c4 (CS24⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp1245 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ023 ∷ CCZ234 ∷ []) ⟫ʷ
wp1245 c4 = pw1 c4 (CCZ023 ∷ []) (CCZ234 ∷ CCZ023 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1246 : Complete 4 → ⟪ (Toff014 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff014 ∷ []) ⟫ʷ
wp1246 c4 = pw2 c4 (Toff014 ∷ Toff314 ∷ []) (Toff314 ∷ Toff014 ∷ []) tt tt Eq.refl

wp1247 : Complete 4 → ⟪ (CS14⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS14⁻ ∷ []) ⟫ʷ
wp1247 c4 = pw3 c4 (CS14⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp1248 : Complete 4 → ⟪ (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ []) ⟫ʷ
wp1248 c4 = pw2 c4 (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff314 ∷ []) tt tt Eq.refl

wp1249 : Complete 4 → ⟪ (CCZ234 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ234 ∷ CCZ034 ∷ []) ⟫ʷ
wp1249 c4 = pw1 c4 (CCZ234 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ234 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1250 : Complete 4 → ⟪ (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ124 ∷ []) ⟫ʷ
wp1250 c4 = pw3 c4 (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (Toff201 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1251 : Complete 4 → ⟪ (CS04 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS04 ∷ []) ⟫ʷ
wp1251 c4 = pw1 c4 (CS04 ∷ Toff203 ∷ []) (Toff203 ∷ CS04 ∷ []) tt tt Eq.refl

wp1252 : Complete 4 → ⟪ (CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp1252 c4 = pw2 c4 (CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp1253 : Complete 4 → ⟪ (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ []) ⟫ʷ
wp1253 c4 = pw1 c4 (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl

wp1254 : Complete 4 → ⟪ (CCZ023 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ234 ∷ CCZ023 ∷ []) ⟫ʷ
wp1254 c4 = pw1 c4 (CCZ023 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ234 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1255 : Complete 4 → ⟪ (CCZ014 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ124 ∷ CCZ014 ∷ []) ⟫ʷ
wp1255 c4 = pw3 c4 (CCZ014 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1256 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ124 ∷ Toff012 ∷ []) ⟫ʷ
wp1256 c4 = pw3 c4 (CCZ124 ∷ []) (Toff012 ∷ CCZ124 ∷ Toff012 ∷ []) tt tt Eq.refl

wp1257 : Complete 4 → ⟪ (CCZ134 ∷ Toff034 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ []) ⟫ʷ
wp1257 c4 = pw2 c4 (CCZ134 ∷ Toff034 ∷ CCZ134 ∷ []) (Toff034 ∷ []) tt tt Eq.refl

wp1258 : Complete 4 → ⟪ (CK40⁻ ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp1258 c4 = pw1 c4 (CK40⁻ ∷ CK40 ∷ []) [] tt tt Eq.refl

wp1259 : Complete 4 → ⟪ (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ []) ⟫ʷ
wp1259 c4 = pw2 c4 (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1260 : Complete 4 → ⟪ (CCZ014 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ CS01 ∷ []) ⟫ʷ
wp1260 c4 = pw2 c4 (CCZ014 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ []) (Toff314 ∷ CS03 ∷ CS01 ∷ []) tt tt Eq.refl

wp1261 : Complete 4 → ⟪ (CS01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) ⟫ʷ
wp1261 c4 = pw3 c4 (CS01 ∷ CCZ014 ∷ []) (CS01 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) tt tt Eq.refl

wp1262 : Complete 4 → ⟪ (CS01 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp1262 c4 = pw2 c4 (CS01 ∷ []) (Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp1263 : Complete 4 → ⟪ (K0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp1263 c4 = pw1 c4 (K0 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp1264 : Complete 4 → ⟪ (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CK40 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK40 ∷ CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ
wp1264 c4 = pw2 c4 (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) tt tt Eq.refl

wp1265 : Complete 4 → ⟪ (CS12 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) ⟫ʷ
wp1265 c4 = pw3 c4 (CS12 ∷ CCZ124 ∷ []) (CS12 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) tt tt Eq.refl

wp1266 : Complete 4 → ⟪ (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
wp1266 c4 = pw0 c4 (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) tt tt Eq.refl

wp1267 : Complete 4 → ⟪ (S0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp1267 c4 = pw1 c4 (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp1268 : Complete 4 → ⟪ (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
wp1268 c4 = pw2 c4 (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) tt tt Eq.refl

wp1269 : Complete 4 → ⟪ (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
wp1269 c4 = pw0 c4 (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) tt tt Eq.refl

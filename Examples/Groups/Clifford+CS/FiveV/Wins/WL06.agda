------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.Wins.WL06 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl1140 : Complete 4 → ⟪ (CCZ123 ∷ CK41 ∷ CCZ123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ []) ⟫ʷ
wl1140 c4 = lw0 c4 (CCZ123 ∷ CK41 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1141 : Complete 4 → ⟪ (CCZ123 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS14 ∷ CCZ123 ∷ []) ⟫ʷ
wl1141 c4 = lw0 c4 (CCZ123 ∷ CS14 ∷ CS14 ∷ []) (CS14 ∷ CS14 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1142 : Complete 4 → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wl1142 c4 = lw0 c4 (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wl1143 : Complete 4 → ⟪ (CX41 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
wl1143 c4 = lw0 c4 (CX41 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ []) tt tt Eq.refl

wl1144 : Complete 4 → ⟪ (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK42 ∷ []) ⟫ʷ
wl1144 c4 = lw0 c4 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK42 ∷ []) tt tt Eq.refl

wl1145 : Complete 4 → ⟪ (CCZ123 ∷ CK42 ∷ CCZ123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ []) ⟫ʷ
wl1145 c4 = lw0 c4 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1146 : Complete 4 → ⟪ (CCZ123 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS24 ∷ CCZ123 ∷ []) ⟫ʷ
wl1146 c4 = lw0 c4 (CCZ123 ∷ CS24 ∷ CS24 ∷ []) (CS24 ∷ CS24 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1147 : Complete 4 → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ []) ⟫ʷ
wl1147 c4 = lw0 c4 (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ []) (CX42 ∷ []) tt tt Eq.refl

wl1148 : Complete 4 → ⟪ (CX42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
wl1148 c4 = lw0 c4 (CX42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS34 ∷ []) tt tt Eq.refl

wl1149 : Complete 4 → ⟪ (CCZ124 ∷ CX34 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ124 ∷ []) ⟫ʷ
wl1149 c4 = lw0 c4 (CCZ124 ∷ CX34 ∷ CCZ123 ∷ []) (CX34 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1150 : Complete 4 → ⟪ (CCZ123 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ123 ∷ CCZ013 ∷ []) ⟫ʷ
wl1150 c4 = lw4 c4 (CCZ123 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ123 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1151 : Complete 4 → ⟪ (CCZ124 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ124 ∷ []) ⟫ʷ
wl1151 c4 = lw0 c4 (CCZ124 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1152 : Complete 4 → ⟪ (CCZ124 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ124 ∷ []) ⟫ʷ
wl1152 c4 = lw0 c4 (CCZ124 ∷ CS13 ∷ []) (CS13 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1153 : Complete 4 → ⟪ (CX34 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ []) ⟫ʷ
wl1153 c4 = lw0 c4 (CX34 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX34 ∷ []) tt tt Eq.refl

wl1154 : Complete 4 → ⟪ (CS01 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS01 ∷ []) ⟫ʷ
wl1154 c4 = lw4 c4 (CS01 ∷ Toff203 ∷ []) (Toff203 ∷ CS01 ∷ []) tt tt Eq.refl

wl1155 : Complete 4 → ⟪ (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wl1155 c4 = lw4 c4 (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl

wl1156 : Complete 4 → ⟪ (CCZ123 ∷ CX43 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ123 ∷ []) ⟫ʷ
wl1156 c4 = lw0 c4 (CCZ123 ∷ CX43 ∷ CCZ124 ∷ []) (CX43 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1157 : Complete 4 → ⟪ (CX43 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ []) ⟫ʷ
wl1157 c4 = lw0 c4 (CX43 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX43 ∷ []) tt tt Eq.refl

wl1158 : Complete 4 → ⟪ (CCZ123 ∷ Toff203 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ123 ∷ []) ⟫ʷ
wl1158 c4 = lw4 c4 (CCZ123 ∷ Toff203 ∷ CCZ013 ∷ []) (Toff203 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1159 : Complete 4 → ⟪ (CCZ124 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Toff124 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ
wl1159 c4 = lw0 c4 (CCZ124 ∷ K1 ∷ []) (K1 ∷ Toff124 ∷ CCZ124 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1160 : Complete 4 → ⟪ (CCZ124 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CK41 ∷ CZ12 ∷ CCZ124 ∷ []) ⟫ʷ
wl1160 c4 = lw0 c4 (CCZ124 ∷ CK41 ∷ []) (CZ12 ∷ CK41 ∷ CZ12 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1161 : Complete 4 → ⟪ (CCZ124 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ124 ∷ []) ⟫ʷ
wl1161 c4 = lw0 c4 (CCZ124 ∷ S4 ∷ []) (S4 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1162 : Complete 4 → ⟪ (K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Toff124 ∷ CCZ124 ∷ CZ12 ∷ CK41 ∷ CZ12 ∷ S4 ∷ []) ⟫ʷ
wl1162 c4 = lw0 c4 (K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ Toff124 ∷ CCZ124 ∷ CZ12 ∷ CK41 ∷ CZ12 ∷ S4 ∷ []) tt tt Eq.refl

wl1163 : Complete 4 → ⟪ (K1 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ K1 ∷ []) ⟫ʷ
wl1163 c4 = lw4 c4 (K1 ∷ Toff203 ∷ []) (Toff203 ∷ K1 ∷ []) tt tt Eq.refl

wl1164 : Complete 4 → ⟪ (CCZ023 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ023 ∷ CCZ123 ∷ []) ⟫ʷ
wl1164 c4 = lw4 c4 (CCZ023 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ023 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1165 : Complete 4 → ⟪ (CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ023 ∷ []) ⟫ʷ
wl1165 c4 = lw4 c4 (CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) (Toff013 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1166 : Complete 4 → ⟪ (CCZ013 ∷ CX21 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ013 ∷ []) ⟫ʷ
wl1166 c4 = lw4 c4 (CCZ013 ∷ CX21 ∷ CCZ023 ∷ []) (CX21 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1167 : Complete 4 → ⟪ (CCZ013 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wl1167 c4 = lw4 c4 (CCZ013 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1168 : Complete 4 → ⟪ (CX21 ∷ CCZ023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wl1168 c4 = lw4 c4 (CX21 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX21 ∷ []) tt tt Eq.refl

wl1169 : Complete 4 → ⟪ (CX42 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
wl1169 c4 = lw0 c4 (CX42 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS14 ∷ []) tt tt Eq.refl

wl1170 : Complete 4 → ⟪ (CCZ013 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ
wl1170 c4 = lw4 c4 (CCZ013 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1171 : Complete 4 → ⟪ (CS23 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS23 ∷ []) ⟫ʷ
wl1171 c4 = lw4 c4 (CS23 ∷ Toff012 ∷ []) (Toff012 ∷ CS23 ∷ []) tt tt Eq.refl

wl1172 : Complete 4 → ⟪ (CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK43 ∷ []) ⟫ʷ
wl1172 c4 = lw0 c4 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK43 ∷ []) tt tt Eq.refl

wl1173 : Complete 4 → ⟪ (CCZ123 ∷ CK43 ∷ CCZ123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ []) ⟫ʷ
wl1173 c4 = lw0 c4 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1174 : Complete 4 → ⟪ (CCZ012 ∷ CX32 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ012 ∷ []) ⟫ʷ
wl1174 c4 = lw4 c4 (CCZ012 ∷ CX32 ∷ CCZ013 ∷ []) (CX32 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1175 : Complete 4 → ⟪ (CX32 ∷ CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
wl1175 c4 = lw4 c4 (CX32 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX32 ∷ []) tt tt Eq.refl

wl1176 : Complete 4 → ⟪ (CCZ123 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS34 ∷ CCZ123 ∷ []) ⟫ʷ
wl1176 c4 = lw0 c4 (CCZ123 ∷ CS34 ∷ CS34 ∷ []) (CS34 ∷ CS34 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1177 : Complete 4 → ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ []) ⟫ʷ
wl1177 c4 = lw0 c4 (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ []) (CX43 ∷ []) tt tt Eq.refl

wl1178 : Complete 4 → ⟪ (CX43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
wl1178 c4 = lw0 c4 (CX43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ []) tt tt Eq.refl

wl1179 : Complete 4 → ⟪ (CX12 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX12 ∷ Toff314 ∷ []) ⟫ʷ
wl1179 c4 = lw0 c4 (CX12 ∷ Toff324 ∷ []) (Toff324 ∷ CX12 ∷ Toff314 ∷ []) tt tt Eq.refl

wl1180 : Complete 4 → ⟪ (Toff314 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff314 ∷ []) ⟫ʷ
wl1180 c4 = lw0 c4 (Toff314 ∷ Toff324 ∷ []) (Toff324 ∷ Toff314 ∷ []) tt tt Eq.refl

wl1181 : Complete 4 → ⟪ (CX12 ∷ Toff314 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
wl1181 c4 = lw0 c4 (CX12 ∷ Toff314 ∷ Toff314 ∷ []) (CX12 ∷ []) tt tt Eq.refl

wl1182 : Complete 4 → ⟪ (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ []) ⟫ʷ
wl1182 c4 = lw0 c4 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl

wl1183 : Complete 4 → ⟪ (CX12 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX12 ∷ []) ⟫ʷ
wl1183 c4 = lw0 c4 (CX12 ∷ Toff314 ∷ []) (Toff314 ∷ CX12 ∷ []) tt tt Eq.refl

wl1184 : Complete 4 → ⟪ (CX21 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX21 ∷ Toff324 ∷ []) ⟫ʷ
wl1184 c4 = lw0 c4 (CX21 ∷ Toff314 ∷ []) (Toff314 ∷ CX21 ∷ Toff324 ∷ []) tt tt Eq.refl

wl1185 : Complete 4 → ⟪ (CX42 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX42 ∷ []) ⟫ʷ
wl1185 c4 = lw0 c4 (CX42 ∷ Toff314 ∷ []) (Toff314 ∷ CX42 ∷ []) tt tt Eq.refl

wl1186 : Complete 4 → ⟪ (CX21 ∷ Toff324 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wl1186 c4 = lw0 c4 (CX21 ∷ Toff324 ∷ Toff324 ∷ []) (CX21 ∷ []) tt tt Eq.refl

wl1187 : Complete 4 → ⟪ (CCZ013 ∷ CZ01 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ013 ∷ []) ⟫ʷ
wl1187 c4 = lw4 c4 (CCZ013 ∷ CZ01 ∷ CX03 ∷ []) (CX03 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1188 : Complete 4 → ⟪ (CCZ013 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ013 ∷ CX03 ∷ []) ⟫ʷ
wl1188 c4 = lw4 c4 (CCZ013 ∷ CZ01 ∷ []) (CX03 ∷ CCZ013 ∷ CX03 ∷ []) tt tt Eq.refl

wl1189 : Complete 4 → ⟪ (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ134 ∷ []) ⟫ʷ
wl1189 c4 = lw0 c4 (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (Toff324 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1190 : Complete 4 → ⟪ (CS12 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS12 ∷ []) ⟫ʷ
wl1190 c4 = lw4 c4 (CS12 ∷ Toff302 ∷ []) (Toff302 ∷ CS12 ∷ []) tt tt Eq.refl

wl1191 : Complete 4 → ⟪ (CS13⁻ ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wl1191 c4 = lw4 c4 (CS13⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1192 : Complete 4 → ⟪ (CCZ013 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CZ01 ∷ CCZ013 ∷ []) ⟫ʷ
wl1192 c4 = lw4 c4 (CCZ013 ∷ Toff301 ∷ []) (Toff301 ∷ CZ01 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1193 : Complete 4 → ⟪ (CS01⁻ ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS01⁻ ∷ []) ⟫ʷ
wl1193 c4 = lw4 c4 (CS01⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl1194 : Complete 4 → ⟪ (CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ CS01⁻ ∷ CZ01 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
wl1194 c4 = lw4 c4 (CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ CS01⁻ ∷ CZ01 ∷ CCZ013 ∷ []) (CS13⁻ ∷ []) tt tt Eq.refl

wl1195 : Complete 4 → ⟪ (CS13 ∷ CS01 ∷ CCZ013 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CS13 ∷ []) ⟫ʷ
wl1195 c4 = lw4 c4 (CS13 ∷ CS01 ∷ CCZ013 ∷ CX03 ∷ []) (CX03 ∷ CS13 ∷ []) tt tt Eq.refl

wl1196 : Complete 4 → ⟪ (CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1196 c4 = lw4 c4 (CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ CX03 ∷ []) (CX03 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1197 : Complete 4 → ⟪ (CCZ013 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ013 ∷ []) ⟫ʷ
wl1197 c4 = lw4 c4 (CCZ013 ∷ CS01 ∷ []) (CS01 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1198 : Complete 4 → ⟪ (CS01 ∷ CS13⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
wl1198 c4 = lw4 c4 (CS01 ∷ CS13⁻ ∷ CS01⁻ ∷ []) (CS13⁻ ∷ []) tt tt Eq.refl

wl1199 : Complete 4 → ⟪ (CCZ013 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wl1199 c4 = lw4 c4 (CCZ013 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1200 : Complete 4 → ⟪ (CS13 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS13 ∷ CS01 ∷ CCZ013 ∷ []) ⟫ʷ
wl1200 c4 = lw4 c4 (CS13 ∷ Toff301 ∷ []) (Toff301 ∷ CS13 ∷ CS01 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1201 : Complete 4 → ⟪ (CS01 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS01 ∷ []) ⟫ʷ
wl1201 c4 = lw4 c4 (CS01 ∷ Toff301 ∷ []) (Toff301 ∷ CS01 ∷ []) tt tt Eq.refl

wl1202 : Complete 4 → ⟪ (CS13 ∷ CS01 ∷ CCZ013 ∷ CS01 ∷ CZ01 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
wl1202 c4 = lw4 c4 (CS13 ∷ CS01 ∷ CCZ013 ∷ CS01 ∷ CZ01 ∷ CCZ013 ∷ []) (CS13 ∷ []) tt tt Eq.refl

wl1203 : Complete 4 → ⟪ (CCZ234 ∷ Toff324 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
wl1203 c4 = lw0 c4 (CCZ234 ∷ Toff324 ∷ CZ24 ∷ []) (Toff324 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1204 : Complete 4 → ⟪ (CCZ234 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CZ24 ∷ CCZ234 ∷ []) ⟫ʷ
wl1204 c4 = lw0 c4 (CCZ234 ∷ Toff324 ∷ []) (Toff324 ∷ CZ24 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1205 : Complete 4 → ⟪ (CX03 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1205 c4 = lw4 c4 (CX03 ∷ CX03 ∷ []) [] tt tt Eq.refl

wl1206 : Complete 4 → ⟪ (CCZ134 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) ⟫ʷ
wl1206 c4 = lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1207 : Complete 4 → ⟪ (CX30 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX30 ∷ []) ⟫ʷ
wl1207 c4 = lw4 c4 (CX30 ∷ Toff023 ∷ []) (Toff023 ∷ CX30 ∷ []) tt tt Eq.refl

wl1208 : Complete 4 → ⟪ (CS13 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CS13 ∷ []) ⟫ʷ
wl1208 c4 = lw4 c4 (CS13 ∷ CX30 ∷ []) (CX30 ∷ CS13 ∷ []) tt tt Eq.refl

wl1209 : Complete 4 → ⟪ (CS13⁻ ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1209 c4 = lw4 c4 (CS13⁻ ∷ CX30 ∷ []) (CX30 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1210 : Complete 4 → ⟪ (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw03 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) ⟫ʷ
wl1210 c4 = lw4 c4 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) tt tt Eq.refl

wl1211 : Complete 4 → ⟪ (CS01 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw03 ∷ CS13 ∷ []) ⟫ʷ
wl1211 c4 = lw4 c4 (CS01 ∷ Sw03 ∷ []) (Sw03 ∷ CS13 ∷ []) tt tt Eq.refl

wl1212 : Complete 4 → ⟪ (CS01⁻ ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw03 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1212 c4 = lw4 c4 (CS01⁻ ∷ Sw03 ∷ []) (Sw03 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1213 : Complete 4 → ⟪ (CCZ023 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ023 ∷ CCZ012 ∷ []) ⟫ʷ
wl1213 c4 = lw4 c4 (CCZ023 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ023 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1214 : Complete 4 → ⟪ (CX42 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX42 ∷ Toff314 ∷ []) ⟫ʷ
wl1214 c4 = lw0 c4 (CX42 ∷ Toff312 ∷ []) (Toff312 ∷ CX42 ∷ Toff314 ∷ []) tt tt Eq.refl

wl1215 : Complete 4 → ⟪ (CX42 ∷ Toff314 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ []) ⟫ʷ
wl1215 c4 = lw0 c4 (CX42 ∷ Toff314 ∷ Toff314 ∷ []) (CX42 ∷ []) tt tt Eq.refl

wl1216 : Complete 4 → ⟪ (CCZ134 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ CCZ123 ∷ []) ⟫ʷ
wl1216 c4 = lw0 c4 (CCZ134 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1217 : Complete 4 → ⟪ (Sw24 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sw24 ∷ []) ⟫ʷ
wl1217 c4 = lw0 c4 (Sw24 ∷ Toff312 ∷ []) (Toff314 ∷ Sw24 ∷ []) tt tt Eq.refl

wl1218 : Complete 4 → ⟪ (CCZ123 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ CCZ134 ∷ []) ⟫ʷ
wl1218 c4 = lw0 c4 (CCZ123 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1219 : Complete 4 → ⟪ (Sw24 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ Sw24 ∷ []) ⟫ʷ
wl1219 c4 = lw0 c4 (Sw24 ∷ Toff134 ∷ []) (Toff123 ∷ Sw24 ∷ []) tt tt Eq.refl

wl1220 : Complete 4 → ⟪ (CCZ134 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ134 ∷ []) ⟫ʷ
wl1220 c4 = lw0 c4 (CCZ134 ∷ CS24 ∷ []) (CS24 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1221 : Complete 4 → ⟪ (CCZ134 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ134 ∷ []) ⟫ʷ
wl1221 c4 = lw0 c4 (CCZ134 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1222 : Complete 4 → ⟪ (CCZ124 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ124 ∷ []) ⟫ʷ
wl1222 c4 = lw0 c4 (CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1223 : Complete 4 → ⟪ (CS01 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS01 ∷ []) ⟫ʷ
wl1223 c4 = lw4 c4 (CS01 ∷ Toff302 ∷ []) (Toff302 ∷ CS01 ∷ []) tt tt Eq.refl

wl1224 : Complete 4 → ⟪ (CS01⁻ ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS01⁻ ∷ []) ⟫ʷ
wl1224 c4 = lw4 c4 (CS01⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl1225 : Complete 4 → ⟪ (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff214 ∷ []) ⟫ʷ
wl1225 c4 = lw0 c4 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (Toff312 ∷ Toff214 ∷ []) tt tt Eq.refl

wl1226 : Complete 4 → ⟪ (CS02⁻ ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS02⁻ ∷ []) ⟫ʷ
wl1226 c4 = lw4 c4 (CS02⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl1227 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) ⟫ʷ
wl1227 c4 = lw0 c4 (CCZ124 ∷ []) (CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1228 : Complete 4 → ⟪ (CX24 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX24 ∷ Toff312 ∷ []) ⟫ʷ
wl1228 c4 = lw0 c4 (CX24 ∷ Toff314 ∷ []) (Toff314 ∷ CX24 ∷ Toff312 ∷ []) tt tt Eq.refl

wl1229 : Complete 4 → ⟪ (CCZ023 ∷ Toff312 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ023 ∷ []) ⟫ʷ
wl1229 c4 = lw4 c4 (CCZ023 ∷ Toff312 ∷ CCZ012 ∷ []) (Toff312 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1230 : Complete 4 → ⟪ (CX24 ∷ Toff312 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ []) ⟫ʷ
wl1230 c4 = lw0 c4 (CX24 ∷ Toff312 ∷ Toff312 ∷ []) (CX24 ∷ []) tt tt Eq.refl

wl1231 : Complete 4 → ⟪ (Sw24 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Sw24 ∷ []) ⟫ʷ
wl1231 c4 = lw0 c4 (Sw24 ∷ Toff314 ∷ []) (Toff312 ∷ Sw24 ∷ []) tt tt Eq.refl

wl1232 : Complete 4 → ⟪ (Sw24 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Sw24 ∷ []) ⟫ʷ
wl1232 c4 = lw0 c4 (Sw24 ∷ Toff123 ∷ []) (Toff134 ∷ Sw24 ∷ []) tt tt Eq.refl

wl1233 : Complete 4 → ⟪ (CX01 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CX01 ∷ []) ⟫ʷ
wl1233 c4 = lw4 c4 (CX01 ∷ Toff302 ∷ []) (Toff302 ∷ CX01 ∷ []) tt tt Eq.refl

wl1234 : Complete 4 → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1234 c4 = lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1235 : Complete 4 → ⟪ (CCZ023 ∷ CZ02 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
wl1235 c4 = lw4 c4 (CCZ023 ∷ CZ02 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1236 : Complete 4 → ⟪ (CCZ023 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ Toff302 ∷ []) ⟫ʷ
wl1236 c4 = lw4 c4 (CCZ023 ∷ CZ02 ∷ []) (Toff302 ∷ CCZ023 ∷ Toff302 ∷ []) tt tt Eq.refl

wl1237 : Complete 4 → ⟪ (CCZ134 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ134 ∷ []) ⟫ʷ
wl1237 c4 = lw0 c4 (CCZ134 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1238 : Complete 4 → ⟪ (CCZ023 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ CZ02 ∷ []) ⟫ʷ
wl1238 c4 = lw4 c4 (CCZ023 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ023 ∷ CZ02 ∷ []) tt tt Eq.refl

wl1239 : Complete 4 → ⟪ (CCZ023 ∷ CZ02 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
wl1239 c4 = lw4 c4 (CCZ023 ∷ CZ02 ∷ Toff302 ∷ CCZ023 ∷ []) (Toff302 ∷ []) tt tt Eq.refl

wl1240 : Complete 4 → ⟪ (CCZ134 ∷ CX24 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ CCZ134 ∷ []) ⟫ʷ
wl1240 c4 = lw0 c4 (CCZ134 ∷ CX24 ∷ CCZ123 ∷ []) (CX24 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1241 : Complete 4 → ⟪ (CCZ123 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ
wl1241 c4 = lw4 c4 (CCZ123 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ123 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1242 : Complete 4 → ⟪ (CX24 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ []) ⟫ʷ
wl1242 c4 = lw0 c4 (CX24 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX24 ∷ []) tt tt Eq.refl

wl1243 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ012 ∷ X4 ∷ []) ⟫ʷ
wl1243 c4 = lw3 c4 (CCZ012 ∷ []) (X4 ∷ CCZ012 ∷ X4 ∷ []) tt tt Eq.refl

wl1244 : Complete 4 → ⟪ (CCZ123 ∷ CX42 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CCZ123 ∷ []) ⟫ʷ
wl1244 c4 = lw0 c4 (CCZ123 ∷ CX42 ∷ CCZ134 ∷ []) (CX42 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1245 : Complete 4 → ⟪ (CX42 ∷ CCZ134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ []) ⟫ʷ
wl1245 c4 = lw0 c4 (CX42 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX42 ∷ []) tt tt Eq.refl

wl1246 : Complete 4 → ⟪ (CCZ123 ∷ Toff302 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ123 ∷ []) ⟫ʷ
wl1246 c4 = lw4 c4 (CCZ123 ∷ Toff302 ∷ CCZ012 ∷ []) (Toff302 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1247 : Complete 4 → ⟪ (CCZ134 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ []) ⟫ʷ
wl1247 c4 = lw0 c4 (CCZ134 ∷ K1 ∷ []) (K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1248 : Complete 4 → ⟪ (CCZ134 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CK41 ∷ CZ13 ∷ CCZ134 ∷ []) ⟫ʷ
wl1248 c4 = lw0 c4 (CCZ134 ∷ CK41 ∷ []) (CZ13 ∷ CK41 ∷ CZ13 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1249 : Complete 4 → ⟪ (CCZ134 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ134 ∷ []) ⟫ʷ
wl1249 c4 = lw0 c4 (CCZ134 ∷ S4 ∷ []) (S4 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1250 : Complete 4 → ⟪ (K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ []) ⟫ʷ
wl1250 c4 = lw0 c4 (K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ []) tt tt Eq.refl

wl1251 : Complete 4 → ⟪ (CCZ012 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ012 ∷ []) ⟫ʷ
wl1251 c4 = lw4 c4 (CCZ012 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1252 : Complete 4 → ⟪ (K1 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ K1 ∷ []) ⟫ʷ
wl1252 c4 = lw4 c4 (K1 ∷ Toff302 ∷ []) (Toff302 ∷ K1 ∷ []) tt tt Eq.refl

wl1253 : Complete 4 → ⟪ (CCZ134 ∷ CZ14 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
wl1253 c4 = lw0 c4 (CCZ134 ∷ CZ14 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1254 : Complete 4 → ⟪ (CCZ134 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ Toff314 ∷ []) ⟫ʷ
wl1254 c4 = lw0 c4 (CCZ134 ∷ CZ14 ∷ []) (Toff314 ∷ CCZ134 ∷ Toff314 ∷ []) tt tt Eq.refl

wl1255 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ CCZ134 ∷ CZ14 ∷ []) ⟫ʷ
wl1255 c4 = lw0 c4 (CCZ134 ∷ []) (CZ14 ∷ CCZ134 ∷ CZ14 ∷ []) tt tt Eq.refl

wl1256 : Complete 4 → ⟪ (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ123 ∷ []) ⟫ʷ
wl1256 c4 = lw4 c4 (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (Toff301 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1257 : Complete 4 → ⟪ (CCZ234 ∷ CX14 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ234 ∷ []) ⟫ʷ
wl1257 c4 = lw0 c4 (CCZ234 ∷ CX14 ∷ CCZ123 ∷ []) (CX14 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1258 : Complete 4 → ⟪ (CCZ123 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ
wl1258 c4 = lw4 c4 (CCZ123 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1259 : Complete 4 → ⟪ (CX14 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wl1259 c4 = lw0 c4 (CX14 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wl1260 : Complete 4 → ⟪ (CS02 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS02 ∷ []) ⟫ʷ
wl1260 c4 = lw4 c4 (CS02 ∷ Toff301 ∷ []) (Toff301 ∷ CS02 ∷ []) tt tt Eq.refl

wl1261 : Complete 4 → ⟪ (CCZ234 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Toff234 ∷ CCZ234 ∷ CCZ234 ∷ []) ⟫ʷ
wl1261 c4 = lw0 c4 (CCZ234 ∷ K2 ∷ []) (K2 ∷ Toff234 ∷ CCZ234 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1262 : Complete 4 → ⟪ (CCZ234 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CK42 ∷ CZ23 ∷ CCZ234 ∷ []) ⟫ʷ
wl1262 c4 = lw0 c4 (CCZ234 ∷ CK42 ∷ []) (CZ23 ∷ CK42 ∷ CZ23 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1263 : Complete 4 → ⟪ (CCZ234 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ234 ∷ []) ⟫ʷ
wl1263 c4 = lw0 c4 (CCZ234 ∷ S4 ∷ []) (S4 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1264 : Complete 4 → ⟪ (K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Toff234 ∷ CCZ234 ∷ CZ23 ∷ CK42 ∷ CZ23 ∷ S4 ∷ []) ⟫ʷ
wl1264 c4 = lw0 c4 (K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ Toff234 ∷ CCZ234 ∷ CZ23 ∷ CK42 ∷ CZ23 ∷ S4 ∷ []) tt tt Eq.refl

wl1265 : Complete 4 → ⟪ (CCZ012 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ012 ∷ []) ⟫ʷ
wl1265 c4 = lw4 c4 (CCZ012 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1266 : Complete 4 → ⟪ (K2 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ K2 ∷ []) ⟫ʷ
wl1266 c4 = lw4 c4 (K2 ∷ Toff301 ∷ []) (Toff301 ∷ K2 ∷ []) tt tt Eq.refl

wl1267 : Complete 4 → ⟪ (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff124 ∷ []) ⟫ʷ
wl1267 c4 = lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ []) tt tt Eq.refl

wl1268 : Complete 4 → ⟪ (S4 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ S4 ∷ []) ⟫ʷ
wl1268 c4 = lw0 c4 (S4 ∷ Toff312 ∷ []) (Toff312 ∷ S4 ∷ []) tt tt Eq.refl

wl1269 : Complete 4 → ⟪ (CCZ012 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ012 ∷ []) ⟫ʷ
wl1269 c4 = lw3 c4 (CCZ012 ∷ S4 ∷ []) (S4 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1270 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) ⟫ʷ
wl1270 c4 = lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) tt tt Eq.refl

wl1271 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ []) ⟫ʷ
wl1271 c4 = lw0 c4 (CCZ134 ∷ []) (CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ []) tt tt Eq.refl

wl1272 : Complete 4 → ⟪ (CCZ013 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ013 ∷ CCZ012 ∷ []) ⟫ʷ
wl1272 c4 = lw4 c4 (CCZ013 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ013 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1273 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) ⟫ʷ
wl1273 c4 = lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) tt tt Eq.refl

wl1274 : Complete 4 → ⟪ (CCZ234 ∷ X4 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ234 ∷ []) ⟫ʷ
wl1274 c4 = lw0 c4 (CCZ234 ∷ X4 ∷ CZ23 ∷ []) (X4 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1275 : Complete 4 → ⟪ (CZ23 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CZ23 ∷ CCZ012 ∷ []) ⟫ʷ
wl1275 c4 = lw4 c4 (CZ23 ∷ Toff301 ∷ []) (Toff301 ∷ CZ23 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1276 : Complete 4 → ⟪ (X4 ∷ CZ23 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ []) ⟫ʷ
wl1276 c4 = lw0 c4 (X4 ∷ CZ23 ∷ CZ23 ∷ []) (X4 ∷ []) tt tt Eq.refl

wl1277 : Complete 4 → ⟪ (CCZ134 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ134 ∷ CCZ124 ∷ []) ⟫ʷ
wl1277 c4 = lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ134 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1278 : Complete 4 → ⟪ (CCZ013 ∷ Toff302 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ013 ∷ []) ⟫ʷ
wl1278 c4 = lw4 c4 (CCZ013 ∷ Toff302 ∷ CCZ012 ∷ []) (Toff302 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1279 : Complete 4 → ⟪ (CCZ134 ∷ X4 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ134 ∷ []) ⟫ʷ
wl1279 c4 = lw0 c4 (CCZ134 ∷ X4 ∷ CZ13 ∷ []) (X4 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1280 : Complete 4 → ⟪ (CZ13 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CZ13 ∷ CCZ012 ∷ []) ⟫ʷ
wl1280 c4 = lw4 c4 (CZ13 ∷ Toff302 ∷ []) (Toff302 ∷ CZ13 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1281 : Complete 4 → ⟪ (CCZ134 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ134 ∷ []) ⟫ʷ
wl1281 c4 = lw0 c4 (CCZ134 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1282 : Complete 4 → ⟪ (X4 ∷ CZ13 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ []) ⟫ʷ
wl1282 c4 = lw0 c4 (X4 ∷ CZ13 ∷ CZ13 ∷ []) (X4 ∷ []) tt tt Eq.refl

wl1283 : Complete 4 → ⟪ (CCZ023 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ023 ∷ CCZ123 ∷ []) ⟫ʷ
wl1283 c4 = lw4 c4 (CCZ023 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ023 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1284 : Complete 4 → ⟪ (CS13 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS13 ∷ []) ⟫ʷ
wl1284 c4 = lw4 c4 (CS13 ∷ Toff012 ∷ []) (Toff012 ∷ CS13 ∷ []) tt tt Eq.refl

wl1285 : Complete 4 → ⟪ (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff234 ∷ []) ⟫ʷ
wl1285 c4 = lw0 c4 (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ []) tt tt Eq.refl

wl1286 : Complete 4 → ⟪ (CCZ123 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ123 ∷ []) ⟫ʷ
wl1286 c4 = lw0 c4 (CCZ123 ∷ S4 ∷ []) (S4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1287 : Complete 4 → ⟪ (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Toff214 ∷ []) ⟫ʷ
wl1287 c4 = lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ []) tt tt Eq.refl

wl1288 : Complete 4 → ⟪ (Toff124 ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ []) ⟫ʷ
wl1288 c4 = lw0 c4 (Toff124 ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ []) tt tt Eq.refl

wl1289 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ []) ⟫ʷ
wl1289 c4 = lw0 c4 (CCZ134 ∷ []) (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1290 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
wl1290 c4 = lw0 c4 (CCZ134 ∷ []) (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) tt tt Eq.refl

wl1291 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wl1291 c4 = lw0 c4 (CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wl1292 : Complete 4 → ⟪ (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ []) ⟫ʷ
wl1292 c4 = lw0 c4 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ []) (CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1293 : Complete 4 → ⟪ (CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl1293 c4 = lw0 c4 (CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ []) (S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1294 : Complete 4 → ⟪ (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ []) ⟫ʷ
wl1294 c4 = lw0 c4 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ []) (CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1295 : Complete 4 → ⟪ (CCZ123 ∷ S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl1295 c4 = lw0 c4 (CCZ123 ∷ S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ []) (S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1296 : Complete 4 → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ []) ⟫ʷ
wl1296 c4 = lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ []) tt tt Eq.refl

wl1297 : Complete 4 → ⟪ (CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl1297 c4 = lw0 c4 (CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1298 : Complete 4 → ⟪ (CS24 ∷ CK42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ
wl1298 c4 = lw0 c4 (CS24 ∷ CK42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ []) tt tt Eq.refl

wl1299 : Complete 4 → ⟪ (CS34 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ
wl1299 c4 = lw0 c4 (CS34 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CS34 ∷ []) tt tt Eq.refl

wl1300 : Complete 4 → ⟪ (CK34 ∷ CK34⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1300 c4 = lw0 c4 (CK34 ∷ CK34⁻ ∷ []) [] tt tt Eq.refl

wl1301 : Complete 4 → ⟪ (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
wl1301 c4 = lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl

wl1302 : Complete 4 → ⟪ (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ []) ⟫ʷ
wl1302 c4 = lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) tt tt Eq.refl

wl1303 : Complete 4 → ⟪ (CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wl1303 c4 = lw0 c4 (CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wl1304 : Complete 4 → ⟪ (CX21 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CX21 ∷ []) ⟫ʷ
wl1304 c4 = lw4 c4 (CX21 ∷ Toff302 ∷ []) (Toff302 ∷ CX21 ∷ []) tt tt Eq.refl

wl1305 : Complete 4 → ⟪ (CCZ134 ∷ CX21 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ134 ∷ []) ⟫ʷ
wl1305 c4 = lw0 c4 (CCZ134 ∷ CX21 ∷ CCZ234 ∷ []) (CX21 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1306 : Complete 4 → ⟪ (CX21 ∷ CCZ234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wl1306 c4 = lw0 c4 (CX21 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX21 ∷ []) tt tt Eq.refl

wl1307 : Complete 4 → ⟪ (CX12 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CX12 ∷ Toff301 ∷ []) ⟫ʷ
wl1307 c4 = lw4 c4 (CX12 ∷ Toff302 ∷ []) (Toff302 ∷ CX12 ∷ Toff301 ∷ []) tt tt Eq.refl

wl1308 : Complete 4 → ⟪ (CX12 ∷ Toff301 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
wl1308 c4 = lw4 c4 (CX12 ∷ Toff301 ∷ Toff301 ∷ []) (CX12 ∷ []) tt tt Eq.refl

wl1309 : Complete 4 → ⟪ (Toff124 ∷ Toff324 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff124 ∷ []) ⟫ʷ
wl1309 c4 = lw0 c4 (Toff124 ∷ Toff324 ∷ Toff312 ∷ []) (Toff312 ∷ Toff124 ∷ []) tt tt Eq.refl

wl1310 : Complete 4 → ⟪ (K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ []) ⟫ʷ
wl1310 c4 = lw0 c4 (K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1⁻ ∷ []) (Toff124 ∷ []) tt tt Eq.refl

wl1311 : Complete 4 → ⟪ (Toff124 ∷ Toff324 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ []) ⟫ʷ
wl1311 c4 = lw0 c4 (Toff124 ∷ Toff324 ∷ Toff324 ∷ []) (Toff124 ∷ []) tt tt Eq.refl

------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL06 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wl1140 : Base 4 → ⟪ (ℓ "交亄交並") ⟫ʷ ≈ ⟪ (ℓ "並交丒亄丢交") ⟫ʷ
wl1140 c4 = lw0 c4 (ℓ "交亄交並") (ℓ "並交丒亄丢交") tt tt Eq.refl

wl1141 : Base 4 → ⟪ (ℓ "交乕乕") ⟫ʷ ≈ ⟪ (ℓ "乕乕交") ⟫ʷ
wl1141 c4 = lw0 c4 (ℓ "交乕乕") (ℓ "乕乕交") tt tt Eq.refl

wl1142 : Base 4 → ⟪ (ℓ "亄乕乕亄丢") ⟫ʷ ≈ ⟪ (ℓ "亃") ⟫ʷ
wl1142 c4 = lw0 c4 (ℓ "亄乕乕亄丢") (ℓ "亃") tt tt Eq.refl

wl1143 : Base 4 → ⟪ (ℓ "亃亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亨亲乏交亄乕乕亄交丢乩") ⟫ʷ
wl1143 c4 = lw0 c4 (ℓ "亃亲乎亲乏") (ℓ "亲乎亨亲乏交亄乕乕亄交丢乩") tt tt Eq.refl

wl1144 : Base 4 → ⟪ (ℓ "交亇交交") ⟫ʷ ≈ ⟪ (ℓ "交亇") ⟫ʷ
wl1144 c4 = lw0 c4 (ℓ "交亇交交") (ℓ "交亇") tt tt Eq.refl

wl1145 : Base 4 → ⟪ (ℓ "交亇交並") ⟫ʷ ≈ ⟪ (ℓ "並交丘亇丢交") ⟫ʷ
wl1145 c4 = lw0 c4 (ℓ "交亇交並") (ℓ "並交丘亇丢交") tt tt Eq.refl

wl1146 : Base 4 → ⟪ (ℓ "交乩乩") ⟫ʷ ≈ ⟪ (ℓ "乩乩交") ⟫ʷ
wl1146 c4 = lw0 c4 (ℓ "交乩乩") (ℓ "乩乩交") tt tt Eq.refl

wl1147 : Base 4 → ⟪ (ℓ "亇乩乩亇丢") ⟫ʷ ≈ ⟪ (ℓ "了") ⟫ʷ
wl1147 c4 = lw0 c4 (ℓ "亇乩乩亇丢") (ℓ "了") tt tt Eq.refl

wl1148 : Base 4 → ⟪ (ℓ "了亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亰亭么交亇乩乩亇交丢乹") ⟫ʷ
wl1148 c4 = lw0 c4 (ℓ "了亭乇亭么") (ℓ "亭乇亰亭么交亇乩乩亇交丢乹") tt tt Eq.refl

wl1149 : Base 4 → ⟪ (ℓ "亨乽交") ⟫ʷ ≈ ⟪ (ℓ "乽亨") ⟫ʷ
wl1149 c4 = lw0 c4 (ℓ "亨乽交") (ℓ "乽亨") tt tt Eq.refl

wl1150 : Base 4 → ⟪ (ℓ "交亚") ⟫ʷ ≈ ⟪ (ℓ "亚交亐") ⟫ʷ
wl1150 c4 = lw4 c4 (ℓ "交亚") (ℓ "亚交亐") tt tt Eq.refl

wl1151 : Base 4 → ⟪ (ℓ "亨乏") ⟫ʷ ≈ ⟪ (ℓ "乏亨") ⟫ʷ
wl1151 c4 = lw0 c4 (ℓ "亨乏") (ℓ "乏亨") tt tt Eq.refl

wl1152 : Base 4 → ⟪ (ℓ "亨乎") ⟫ʷ ≈ ⟪ (ℓ "乎亨") ⟫ʷ
wl1152 c4 = lw0 c4 (ℓ "亨乎") (ℓ "乎亨") tt tt Eq.refl

wl1153 : Base 4 → ⟪ (ℓ "乽交交") ⟫ʷ ≈ ⟪ (ℓ "乽") ⟫ʷ
wl1153 c4 = lw0 c4 (ℓ "乽交交") (ℓ "乽") tt tt Eq.refl

wl1154 : Base 4 → ⟪ (ℓ "丨亚") ⟫ʷ ≈ ⟪ (ℓ "亚丨") ⟫ʷ
wl1154 c4 = lw4 c4 (ℓ "丨亚") (ℓ "亚丨") tt tt Eq.refl

wl1155 : Base 4 → ⟪ (ℓ "亘亙个亙亘个") ⟫ʷ ≈ ⟪ (ℓ "交") ⟫ʷ
wl1155 c4 = lw4 c4 (ℓ "亘亙个亙亘个") (ℓ "交") tt tt Eq.refl

wl1156 : Base 4 → ⟪ (ℓ "交争亨") ⟫ʷ ≈ ⟪ (ℓ "争交") ⟫ʷ
wl1156 c4 = lw0 c4 (ℓ "交争亨") (ℓ "争交") tt tt Eq.refl

wl1157 : Base 4 → ⟪ (ℓ "争亨亨") ⟫ʷ ≈ ⟪ (ℓ "争") ⟫ʷ
wl1157 c4 = lw0 c4 (ℓ "争亨亨") (ℓ "争") tt tt Eq.refl

wl1158 : Base 4 → ⟪ (ℓ "交亚亐") ⟫ʷ ≈ ⟪ (ℓ "亚交") ⟫ʷ
wl1158 c4 = lw4 c4 (ℓ "交亚亐") (ℓ "亚交") tt tt Eq.refl

wl1159 : Base 4 → ⟪ (ℓ "亨丒") ⟫ʷ ≈ ⟪ (ℓ "丒亩亨亨") ⟫ʷ
wl1159 c4 = lw0 c4 (ℓ "亨丒") (ℓ "丒亩亨亨") tt tt Eq.refl

wl1160 : Base 4 → ⟪ (ℓ "亨亄") ⟫ʷ ≈ ⟪ (ℓ "义亄义亨") ⟫ʷ
wl1160 c4 = lw0 c4 (ℓ "亨亄") (ℓ "义亄义亨") tt tt Eq.refl

wl1161 : Base 4 → ⟪ (ℓ "亨丢") ⟫ʷ ≈ ⟪ (ℓ "丢亨") ⟫ʷ
wl1161 c4 = lw0 c4 (ℓ "亨丢") (ℓ "丢亨") tt tt Eq.refl

wl1162 : Base 4 → ⟪ (ℓ "丒亄丢") ⟫ʷ ≈ ⟪ (ℓ "丒亩亨义亄义丢") ⟫ʷ
wl1162 c4 = lw0 c4 (ℓ "丒亄丢") (ℓ "丒亩亨义亄义丢") tt tt Eq.refl

wl1163 : Base 4 → ⟪ (ℓ "丒亚") ⟫ʷ ≈ ⟪ (ℓ "亚丒") ⟫ʷ
wl1163 c4 = lw4 c4 (ℓ "丒亚") (ℓ "亚丒") tt tt Eq.refl

wl1164 : Base 4 → ⟪ (ℓ "亘云") ⟫ʷ ≈ ⟪ (ℓ "云亘交") ⟫ʷ
wl1164 c4 = lw4 c4 (ℓ "亘云") (ℓ "云亘交") tt tt Eq.refl

wl1165 : Base 4 → ⟪ (ℓ "亘云交") ⟫ʷ ≈ ⟪ (ℓ "云亘") ⟫ʷ
wl1165 c4 = lw4 c4 (ℓ "亘云交") (ℓ "云亘") tt tt Eq.refl

wl1166 : Base 4 → ⟪ (ℓ "亐也亘") ⟫ʷ ≈ ⟪ (ℓ "也亐") ⟫ʷ
wl1166 c4 = lw4 c4 (ℓ "亐也亘") (ℓ "也亐") tt tt Eq.refl

wl1167 : Base 4 → ⟪ (ℓ "亐乣") ⟫ʷ ≈ ⟪ (ℓ "乣亐") ⟫ʷ
wl1167 c4 = lw4 c4 (ℓ "亐乣") (ℓ "乣亐") tt tt Eq.refl

wl1168 : Base 4 → ⟪ (ℓ "也亘亘") ⟫ʷ ≈ ⟪ (ℓ "也") ⟫ʷ
wl1168 c4 = lw4 c4 (ℓ "也亘亘") (ℓ "也") tt tt Eq.refl

wl1169 : Base 4 → ⟪ (ℓ "了亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亨亲乏交亇乩乩亇交丢乕") ⟫ʷ
wl1169 c4 = lw0 c4 (ℓ "了亲乎亲乏") (ℓ "亲乎亨亲乏交亇乩乩亇交丢乕") tt tt Eq.refl

wl1170 : Base 4 → ⟪ (ℓ "亐亍") ⟫ʷ ≈ ⟪ (ℓ "亍亐交") ⟫ʷ
wl1170 c4 = lw4 c4 (ℓ "亐亍") (ℓ "亍亐交") tt tt Eq.refl

wl1171 : Base 4 → ⟪ (ℓ "乢亍") ⟫ʷ ≈ ⟪ (ℓ "亍乢") ⟫ʷ
wl1171 c4 = lw4 c4 (ℓ "乢亍") (ℓ "亍乢") tt tt Eq.refl

wl1172 : Base 4 → ⟪ (ℓ "交亊交交") ⟫ʷ ≈ ⟪ (ℓ "交亊") ⟫ʷ
wl1172 c4 = lw0 c4 (ℓ "交亊交交") (ℓ "交亊") tt tt Eq.refl

wl1173 : Base 4 → ⟪ (ℓ "交亊交並") ⟫ʷ ≈ ⟪ (ℓ "並交丞亊丢交") ⟫ʷ
wl1173 c4 = lw0 c4 (ℓ "交亊交並") (ℓ "並交丞亊丢交") tt tt Eq.refl

wl1174 : Base 4 → ⟪ (ℓ "二乶亐") ⟫ʷ ≈ ⟪ (ℓ "乶二") ⟫ʷ
wl1174 c4 = lw4 c4 (ℓ "二乶亐") (ℓ "乶二") tt tt Eq.refl

wl1175 : Base 4 → ⟪ (ℓ "乶亐亐") ⟫ʷ ≈ ⟪ (ℓ "乶") ⟫ʷ
wl1175 c4 = lw4 c4 (ℓ "乶亐亐") (ℓ "乶") tt tt Eq.refl

wl1176 : Base 4 → ⟪ (ℓ "交乹乹") ⟫ʷ ≈ ⟪ (ℓ "乹乹交") ⟫ʷ
wl1176 c4 = lw0 c4 (ℓ "交乹乹") (ℓ "乹乹交") tt tt Eq.refl

wl1177 : Base 4 → ⟪ (ℓ "亊乹乹亊丢") ⟫ʷ ≈ ⟪ (ℓ "争") ⟫ʷ
wl1177 c4 = lw0 c4 (ℓ "亊乹乹亊丢") (ℓ "争") tt tt Eq.refl

wl1178 : Base 4 → ⟪ (ℓ "争亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亰亭么交亊乹乹亊交丢乩") ⟫ʷ
wl1178 c4 = lw0 c4 (ℓ "争亭乇亭么") (ℓ "亭乇亰亭么交亊乹乹亊交丢乩") tt tt Eq.refl

wl1179 : Base 4 → ⟪ (ℓ "之亲") ⟫ʷ ≈ ⟪ (ℓ "亲之亮") ⟫ʷ
wl1179 c4 = lw0 c4 (ℓ "之亲") (ℓ "亲之亮") tt tt Eq.refl

wl1180 : Base 4 → ⟪ (ℓ "亮亲") ⟫ʷ ≈ ⟪ (ℓ "亲亮") ⟫ʷ
wl1180 c4 = lw0 c4 (ℓ "亮亲") (ℓ "亲亮") tt tt Eq.refl

wl1181 : Base 4 → ⟪ (ℓ "之亮亮") ⟫ʷ ≈ ⟪ (ℓ "之") ⟫ʷ
wl1181 c4 = lw0 c4 (ℓ "之亮亮") (ℓ "之") tt tt Eq.refl

wl1182 : Base 4 → ⟪ (ℓ "丞乕乳乖乳乹丟") ⟫ʷ ≈ ⟪ (ℓ "亮") ⟫ʷ
wl1182 c4 = lw0 c4 (ℓ "丞乕乳乖乳乹丟") (ℓ "亮") tt tt Eq.refl

wl1183 : Base 4 → ⟪ (ℓ "之亮") ⟫ʷ ≈ ⟪ (ℓ "亮之") ⟫ʷ
wl1183 c4 = lw0 c4 (ℓ "之亮") (ℓ "亮之") tt tt Eq.refl

wl1184 : Base 4 → ⟪ (ℓ "也亮") ⟫ʷ ≈ ⟪ (ℓ "亮也亲") ⟫ʷ
wl1184 c4 = lw0 c4 (ℓ "也亮") (ℓ "亮也亲") tt tt Eq.refl

wl1185 : Base 4 → ⟪ (ℓ "了亮") ⟫ʷ ≈ ⟪ (ℓ "亮了") ⟫ʷ
wl1185 c4 = lw0 c4 (ℓ "了亮") (ℓ "亮了") tt tt Eq.refl

wl1186 : Base 4 → ⟪ (ℓ "也亲亲") ⟫ʷ ≈ ⟪ (ℓ "也") ⟫ʷ
wl1186 c4 = lw0 c4 (ℓ "也亲亲") (ℓ "也") tt tt Eq.refl

wl1187 : Base 4 → ⟪ (ℓ "亐个为") ⟫ʷ ≈ ⟪ (ℓ "为亐") ⟫ʷ
wl1187 c4 = lw4 c4 (ℓ "亐个为") (ℓ "为亐") tt tt Eq.refl

wl1188 : Base 4 → ⟪ (ℓ "亐个") ⟫ʷ ≈ ⟪ (ℓ "为亐为") ⟫ʷ
wl1188 c4 = lw4 c4 (ℓ "亐个") (ℓ "为亐为") tt tt Eq.refl

wl1189 : Base 4 → ⟪ (ℓ "京亲亨") ⟫ʷ ≈ ⟪ (ℓ "亲京") ⟫ʷ
wl1189 c4 = lw0 c4 (ℓ "京亲亨") (ℓ "亲京") tt tt Eq.refl

wl1190 : Base 4 → ⟪ (ℓ "乇些") ⟫ʷ ≈ ⟪ (ℓ "些乇") ⟫ʷ
wl1190 c4 = lw4 c4 (ℓ "乇些") (ℓ "些乇") tt tt Eq.refl

wl1191 : Base 4 → ⟪ (ℓ "乏亓") ⟫ʷ ≈ ⟪ (ℓ "亓乏丩亐") ⟫ʷ
wl1191 c4 = lw4 c4 (ℓ "乏亓") (ℓ "亓乏丩亐") tt tt Eq.refl

wl1192 : Base 4 → ⟪ (ℓ "亐亓") ⟫ʷ ≈ ⟪ (ℓ "亓个亐") ⟫ʷ
wl1192 c4 = lw4 c4 (ℓ "亐亓") (ℓ "亓个亐") tt tt Eq.refl

wl1193 : Base 4 → ⟪ (ℓ "丩亓") ⟫ʷ ≈ ⟪ (ℓ "亓丩") ⟫ʷ
wl1193 c4 = lw4 c4 (ℓ "丩亓") (ℓ "亓丩") tt tt Eq.refl

wl1194 : Base 4 → ⟪ (ℓ "乏丩亐丩个亐") ⟫ʷ ≈ ⟪ (ℓ "乏") ⟫ʷ
wl1194 c4 = lw4 c4 (ℓ "乏丩亐丩个亐") (ℓ "乏") tt tt Eq.refl

wl1195 : Base 4 → ⟪ (ℓ "乎丨亐为") ⟫ʷ ≈ ⟪ (ℓ "为乎") ⟫ʷ
wl1195 c4 = lw4 c4 (ℓ "乎丨亐为") (ℓ "为乎") tt tt Eq.refl

wl1196 : Base 4 → ⟪ (ℓ "乏丩亐为") ⟫ʷ ≈ ⟪ (ℓ "为乏") ⟫ʷ
wl1196 c4 = lw4 c4 (ℓ "乏丩亐为") (ℓ "为乏") tt tt Eq.refl

wl1197 : Base 4 → ⟪ (ℓ "亐丨") ⟫ʷ ≈ ⟪ (ℓ "丨亐") ⟫ʷ
wl1197 c4 = lw4 c4 (ℓ "亐丨") (ℓ "丨亐") tt tt Eq.refl

wl1198 : Base 4 → ⟪ (ℓ "丨乏丩") ⟫ʷ ≈ ⟪ (ℓ "乏") ⟫ʷ
wl1198 c4 = lw4 c4 (ℓ "丨乏丩") (ℓ "乏") tt tt Eq.refl

wl1199 : Base 4 → ⟪ (ℓ "亐乏") ⟫ʷ ≈ ⟪ (ℓ "乏亐") ⟫ʷ
wl1199 c4 = lw4 c4 (ℓ "亐乏") (ℓ "乏亐") tt tt Eq.refl

wl1200 : Base 4 → ⟪ (ℓ "乎亓") ⟫ʷ ≈ ⟪ (ℓ "亓乎丨亐") ⟫ʷ
wl1200 c4 = lw4 c4 (ℓ "乎亓") (ℓ "亓乎丨亐") tt tt Eq.refl

wl1201 : Base 4 → ⟪ (ℓ "丨亓") ⟫ʷ ≈ ⟪ (ℓ "亓丨") ⟫ʷ
wl1201 c4 = lw4 c4 (ℓ "丨亓") (ℓ "亓丨") tt tt Eq.refl

wl1202 : Base 4 → ⟪ (ℓ "乎丨亐丨个亐") ⟫ʷ ≈ ⟪ (ℓ "乎") ⟫ʷ
wl1202 c4 = lw4 c4 (ℓ "乎丨亐丨个亐") (ℓ "乎") tt tt Eq.refl

wl1203 : Base 4 → ⟪ (ℓ "亰亲乫") ⟫ʷ ≈ ⟪ (ℓ "亲亰") ⟫ʷ
wl1203 c4 = lw0 c4 (ℓ "亰亲乫") (ℓ "亲亰") tt tt Eq.refl

wl1204 : Base 4 → ⟪ (ℓ "亰亲") ⟫ʷ ≈ ⟪ (ℓ "亲乫亰") ⟫ʷ
wl1204 c4 = lw0 c4 (ℓ "亰亲") (ℓ "亲乫亰") tt tt Eq.refl

wl1205 : Base 4 → ⟪ (ℓ "为为") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1205 c4 = lw4 c4 (ℓ "为为") [] tt tt Eq.refl

wl1206 : Base 4 → ⟪ (ℓ "京亲") ⟫ʷ ≈ ⟪ (ℓ "亲亨京") ⟫ʷ
wl1206 c4 = lw0 c4 (ℓ "京亲") (ℓ "亲亨京") tt tt Eq.refl

wl1207 : Base 4 → ⟪ (ℓ "买亙") ⟫ʷ ≈ ⟪ (ℓ "亙买") ⟫ʷ
wl1207 c4 = lw4 c4 (ℓ "买亙") (ℓ "亙买") tt tt Eq.refl

wl1208 : Base 4 → ⟪ (ℓ "乎买") ⟫ʷ ≈ ⟪ (ℓ "买乎") ⟫ʷ
wl1208 c4 = lw4 c4 (ℓ "乎买") (ℓ "买乎") tt tt Eq.refl

wl1209 : Base 4 → ⟪ (ℓ "乏买") ⟫ʷ ≈ ⟪ (ℓ "买乏") ⟫ʷ
wl1209 c4 = lw4 c4 (ℓ "乏买") (ℓ "买乏") tt tt Eq.refl

wl1210 : Base 4 → ⟪ (ℓ "交亥个亥交个丹") ⟫ʷ ≈ ⟪ (ℓ "丹二于乐于二乐") ⟫ʷ
wl1210 c4 = lw4 c4 (ℓ "交亥个亥交个丹") (ℓ "丹二于乐于二乐") tt tt Eq.refl

wl1211 : Base 4 → ⟪ (ℓ "丨丹") ⟫ʷ ≈ ⟪ (ℓ "丹乎") ⟫ʷ
wl1211 c4 = lw4 c4 (ℓ "丨丹") (ℓ "丹乎") tt tt Eq.refl

wl1212 : Base 4 → ⟪ (ℓ "丩丹") ⟫ʷ ≈ ⟪ (ℓ "丹乏") ⟫ʷ
wl1212 c4 = lw4 c4 (ℓ "丩丹") (ℓ "丹乏") tt tt Eq.refl

wl1213 : Base 4 → ⟪ (ℓ "亘产") ⟫ʷ ≈ ⟪ (ℓ "产亘二") ⟫ʷ
wl1213 c4 = lw4 c4 (ℓ "亘产") (ℓ "产亘二") tt tt Eq.refl

wl1214 : Base 4 → ⟪ (ℓ "了产") ⟫ʷ ≈ ⟪ (ℓ "产了亮") ⟫ʷ
wl1214 c4 = lw0 c4 (ℓ "了产") (ℓ "产了亮") tt tt Eq.refl

wl1215 : Base 4 → ⟪ (ℓ "了亮亮") ⟫ʷ ≈ ⟪ (ℓ "了") ⟫ʷ
wl1215 c4 = lw0 c4 (ℓ "了亮亮") (ℓ "了") tt tt Eq.refl

wl1216 : Base 4 → ⟪ (ℓ "京乬") ⟫ʷ ≈ ⟪ (ℓ "乬交") ⟫ʷ
wl1216 c4 = lw0 c4 (ℓ "京乬") (ℓ "乬交") tt tt Eq.refl

wl1217 : Base 4 → ⟪ (ℓ "乬产") ⟫ʷ ≈ ⟪ (ℓ "亮乬") ⟫ʷ
wl1217 c4 = lw0 c4 (ℓ "乬产") (ℓ "亮乬") tt tt Eq.refl

wl1218 : Base 4 → ⟪ (ℓ "交乬") ⟫ʷ ≈ ⟪ (ℓ "乬京") ⟫ʷ
wl1218 c4 = lw0 c4 (ℓ "交乬") (ℓ "乬京") tt tt Eq.refl

wl1219 : Base 4 → ⟪ (ℓ "乬亭") ⟫ʷ ≈ ⟪ (ℓ "亥乬") ⟫ʷ
wl1219 c4 = lw0 c4 (ℓ "乬亭") (ℓ "亥乬") tt tt Eq.refl

wl1220 : Base 4 → ⟪ (ℓ "京乩") ⟫ʷ ≈ ⟪ (ℓ "乩京") ⟫ʷ
wl1220 c4 = lw0 c4 (ℓ "京乩") (ℓ "乩京") tt tt Eq.refl

wl1221 : Base 4 → ⟪ (ℓ "京乪") ⟫ʷ ≈ ⟪ (ℓ "乪京") ⟫ʷ
wl1221 c4 = lw0 c4 (ℓ "京乪") (ℓ "乪京") tt tt Eq.refl

wl1222 : Base 4 → ⟪ (ℓ "亨京") ⟫ʷ ≈ ⟪ (ℓ "京亨") ⟫ʷ
wl1222 c4 = lw0 c4 (ℓ "亨京") (ℓ "京亨") tt tt Eq.refl

wl1223 : Base 4 → ⟪ (ℓ "丨些") ⟫ʷ ≈ ⟪ (ℓ "些丨") ⟫ʷ
wl1223 c4 = lw4 c4 (ℓ "丨些") (ℓ "些丨") tt tt Eq.refl

wl1224 : Base 4 → ⟪ (ℓ "丩些") ⟫ʷ ≈ ⟪ (ℓ "些丩") ⟫ʷ
wl1224 c4 = lw4 c4 (ℓ "丩些") (ℓ "些丩") tt tt Eq.refl

wl1225 : Base 4 → ⟪ (ℓ "亪亮产") ⟫ʷ ≈ ⟪ (ℓ "产亪") ⟫ʷ
wl1225 c4 = lw0 c4 (ℓ "亪亮产") (ℓ "产亪") tt tt Eq.refl

wl1226 : Base 4 → ⟪ (ℓ "丰产") ⟫ʷ ≈ ⟪ (ℓ "产丰") ⟫ʷ
wl1226 c4 = lw4 c4 (ℓ "丰产") (ℓ "产丰") tt tt Eq.refl

wl1227 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "亰亨亰") ⟫ʷ
wl1227 c4 = lw0 c4 (ℓ "亨") (ℓ "亰亨亰") tt tt Eq.refl

wl1228 : Base 4 → ⟪ (ℓ "乭亮") ⟫ʷ ≈ ⟪ (ℓ "亮乭产") ⟫ʷ
wl1228 c4 = lw0 c4 (ℓ "乭亮") (ℓ "亮乭产") tt tt Eq.refl

wl1229 : Base 4 → ⟪ (ℓ "亘产二") ⟫ʷ ≈ ⟪ (ℓ "产亘") ⟫ʷ
wl1229 c4 = lw4 c4 (ℓ "亘产二") (ℓ "产亘") tt tt Eq.refl

wl1230 : Base 4 → ⟪ (ℓ "乭产产") ⟫ʷ ≈ ⟪ (ℓ "乭") ⟫ʷ
wl1230 c4 = lw0 c4 (ℓ "乭产产") (ℓ "乭") tt tt Eq.refl

wl1231 : Base 4 → ⟪ (ℓ "乬亮") ⟫ʷ ≈ ⟪ (ℓ "产乬") ⟫ʷ
wl1231 c4 = lw0 c4 (ℓ "乬亮") (ℓ "产乬") tt tt Eq.refl

wl1232 : Base 4 → ⟪ (ℓ "乬亥") ⟫ʷ ≈ ⟪ (ℓ "亭乬") ⟫ʷ
wl1232 c4 = lw0 c4 (ℓ "乬亥") (ℓ "亭乬") tt tt Eq.refl

wl1233 : Base 4 → ⟪ (ℓ "丬些") ⟫ʷ ≈ ⟪ (ℓ "些丬") ⟫ʷ
wl1233 c4 = lw4 c4 (ℓ "丬些") (ℓ "些丬") tt tt Eq.refl

wl1234 : Base 4 → ⟪ (ℓ "亭乇亭么亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏亭乇亭么") ⟫ʷ
wl1234 c4 = lw0 c4 (ℓ "亭乇亭么亲乎亲乏") (ℓ "亲乎亲乏亭乇亭么") tt tt Eq.refl

wl1235 : Base 4 → ⟪ (ℓ "亘丱些") ⟫ʷ ≈ ⟪ (ℓ "些亘") ⟫ʷ
wl1235 c4 = lw4 c4 (ℓ "亘丱些") (ℓ "些亘") tt tt Eq.refl

wl1236 : Base 4 → ⟪ (ℓ "亘丱") ⟫ʷ ≈ ⟪ (ℓ "些亘些") ⟫ʷ
wl1236 c4 = lw4 c4 (ℓ "亘丱") (ℓ "些亘些") tt tt Eq.refl

wl1237 : Base 4 → ⟪ (ℓ "京乣") ⟫ʷ ≈ ⟪ (ℓ "乣京") ⟫ʷ
wl1237 c4 = lw0 c4 (ℓ "京乣") (ℓ "乣京") tt tt Eq.refl

wl1238 : Base 4 → ⟪ (ℓ "亘些") ⟫ʷ ≈ ⟪ (ℓ "些亘丱") ⟫ʷ
wl1238 c4 = lw4 c4 (ℓ "亘些") (ℓ "些亘丱") tt tt Eq.refl

wl1239 : Base 4 → ⟪ (ℓ "亘丱些亘") ⟫ʷ ≈ ⟪ (ℓ "些") ⟫ʷ
wl1239 c4 = lw4 c4 (ℓ "亘丱些亘") (ℓ "些") tt tt Eq.refl

wl1240 : Base 4 → ⟪ (ℓ "京乭交") ⟫ʷ ≈ ⟪ (ℓ "乭京") ⟫ʷ
wl1240 c4 = lw0 c4 (ℓ "京乭交") (ℓ "乭京") tt tt Eq.refl

wl1241 : Base 4 → ⟪ (ℓ "交些") ⟫ʷ ≈ ⟪ (ℓ "些交二") ⟫ʷ
wl1241 c4 = lw4 c4 (ℓ "交些") (ℓ "些交二") tt tt Eq.refl

wl1242 : Base 4 → ⟪ (ℓ "乭交交") ⟫ʷ ≈ ⟪ (ℓ "乭") ⟫ʷ
wl1242 c4 = lw0 c4 (ℓ "乭交交") (ℓ "乭") tt tt Eq.refl

wl1243 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "並二並") ⟫ʷ
wl1243 c4 = lw3 c4 (ℓ "二") (ℓ "並二並") tt tt Eq.refl

wl1244 : Base 4 → ⟪ (ℓ "交了京") ⟫ʷ ≈ ⟪ (ℓ "了交") ⟫ʷ
wl1244 c4 = lw0 c4 (ℓ "交了京") (ℓ "了交") tt tt Eq.refl

wl1245 : Base 4 → ⟪ (ℓ "了京京") ⟫ʷ ≈ ⟪ (ℓ "了") ⟫ʷ
wl1245 c4 = lw0 c4 (ℓ "了京京") (ℓ "了") tt tt Eq.refl

wl1246 : Base 4 → ⟪ (ℓ "交些二") ⟫ʷ ≈ ⟪ (ℓ "些交") ⟫ʷ
wl1246 c4 = lw4 c4 (ℓ "交些二") (ℓ "些交") tt tt Eq.refl

wl1247 : Base 4 → ⟪ (ℓ "京丒") ⟫ʷ ≈ ⟪ (ℓ "丒亭京京") ⟫ʷ
wl1247 c4 = lw0 c4 (ℓ "京丒") (ℓ "丒亭京京") tt tt Eq.refl

wl1248 : Base 4 → ⟪ (ℓ "京亄") ⟫ʷ ≈ ⟪ (ℓ "乐亄乐京") ⟫ʷ
wl1248 c4 = lw0 c4 (ℓ "京亄") (ℓ "乐亄乐京") tt tt Eq.refl

wl1249 : Base 4 → ⟪ (ℓ "京丢") ⟫ʷ ≈ ⟪ (ℓ "丢京") ⟫ʷ
wl1249 c4 = lw0 c4 (ℓ "京丢") (ℓ "丢京") tt tt Eq.refl

wl1250 : Base 4 → ⟪ (ℓ "丒亄丢") ⟫ʷ ≈ ⟪ (ℓ "丒亭京乐亄乐丢") ⟫ʷ
wl1250 c4 = lw0 c4 (ℓ "丒亄丢") (ℓ "丒亭京乐亄乐丢") tt tt Eq.refl

wl1251 : Base 4 → ⟪ (ℓ "二些") ⟫ʷ ≈ ⟪ (ℓ "些二") ⟫ʷ
wl1251 c4 = lw4 c4 (ℓ "二些") (ℓ "些二") tt tt Eq.refl

wl1252 : Base 4 → ⟪ (ℓ "丒些") ⟫ʷ ≈ ⟪ (ℓ "些丒") ⟫ʷ
wl1252 c4 = lw4 c4 (ℓ "丒些") (ℓ "些丒") tt tt Eq.refl

wl1253 : Base 4 → ⟪ (ℓ "京乗亮") ⟫ʷ ≈ ⟪ (ℓ "亮京") ⟫ʷ
wl1253 c4 = lw0 c4 (ℓ "京乗亮") (ℓ "亮京") tt tt Eq.refl

wl1254 : Base 4 → ⟪ (ℓ "京乗") ⟫ʷ ≈ ⟪ (ℓ "亮京亮") ⟫ʷ
wl1254 c4 = lw0 c4 (ℓ "京乗") (ℓ "亮京亮") tt tt Eq.refl

wl1255 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "乗京乗") ⟫ʷ
wl1255 c4 = lw0 c4 (ℓ "京") (ℓ "乗京乗") tt tt Eq.refl

wl1256 : Base 4 → ⟪ (ℓ "交亓二") ⟫ʷ ≈ ⟪ (ℓ "亓交") ⟫ʷ
wl1256 c4 = lw4 c4 (ℓ "交亓二") (ℓ "亓交") tt tt Eq.refl

wl1257 : Base 4 → ⟪ (ℓ "亰乙交") ⟫ʷ ≈ ⟪ (ℓ "乙亰") ⟫ʷ
wl1257 c4 = lw0 c4 (ℓ "亰乙交") (ℓ "乙亰") tt tt Eq.refl

wl1258 : Base 4 → ⟪ (ℓ "交亓") ⟫ʷ ≈ ⟪ (ℓ "亓交二") ⟫ʷ
wl1258 c4 = lw4 c4 (ℓ "交亓") (ℓ "亓交二") tt tt Eq.refl

wl1259 : Base 4 → ⟪ (ℓ "乙交交") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wl1259 c4 = lw0 c4 (ℓ "乙交交") (ℓ "乙") tt tt Eq.refl

wl1260 : Base 4 → ⟪ (ℓ "丯亓") ⟫ʷ ≈ ⟪ (ℓ "亓丯") ⟫ʷ
wl1260 c4 = lw4 c4 (ℓ "丯亓") (ℓ "亓丯") tt tt Eq.refl

wl1261 : Base 4 → ⟪ (ℓ "亰丘") ⟫ʷ ≈ ⟪ (ℓ "丘亱亰亰") ⟫ʷ
wl1261 c4 = lw0 c4 (ℓ "亰丘") (ℓ "丘亱亰亰") tt tt Eq.refl

wl1262 : Base 4 → ⟪ (ℓ "亰亇") ⟫ʷ ≈ ⟪ (ℓ "乤亇乤亰") ⟫ʷ
wl1262 c4 = lw0 c4 (ℓ "亰亇") (ℓ "乤亇乤亰") tt tt Eq.refl

wl1263 : Base 4 → ⟪ (ℓ "亰丢") ⟫ʷ ≈ ⟪ (ℓ "丢亰") ⟫ʷ
wl1263 c4 = lw0 c4 (ℓ "亰丢") (ℓ "丢亰") tt tt Eq.refl

wl1264 : Base 4 → ⟪ (ℓ "丘亇丢") ⟫ʷ ≈ ⟪ (ℓ "丘亱亰乤亇乤丢") ⟫ʷ
wl1264 c4 = lw0 c4 (ℓ "丘亇丢") (ℓ "丘亱亰乤亇乤丢") tt tt Eq.refl

wl1265 : Base 4 → ⟪ (ℓ "二亓") ⟫ʷ ≈ ⟪ (ℓ "亓二") ⟫ʷ
wl1265 c4 = lw4 c4 (ℓ "二亓") (ℓ "亓二") tt tt Eq.refl

wl1266 : Base 4 → ⟪ (ℓ "丘亓") ⟫ʷ ≈ ⟪ (ℓ "亓丘") ⟫ʷ
wl1266 c4 = lw4 c4 (ℓ "丘亓") (ℓ "亓丘") tt tt Eq.refl

wl1267 : Base 4 → ⟪ (ℓ "亇亨亇丢亄亨亄丢") ⟫ʷ ≈ ⟪ (ℓ "亪亩") ⟫ʷ
wl1267 c4 = lw0 c4 (ℓ "亇亨亇丢亄亨亄丢") (ℓ "亪亩") tt tt Eq.refl

wl1268 : Base 4 → ⟪ (ℓ "丢产") ⟫ʷ ≈ ⟪ (ℓ "产丢") ⟫ʷ
wl1268 c4 = lw0 c4 (ℓ "丢产") (ℓ "产丢") tt tt Eq.refl

wl1269 : Base 4 → ⟪ (ℓ "二丢") ⟫ʷ ≈ ⟪ (ℓ "丢二") ⟫ʷ
wl1269 c4 = lw3 c4 (ℓ "二丢") (ℓ "丢二") tt tt Eq.refl

wl1270 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "丶乜丷乜乢") ⟫ʷ
wl1270 c4 = lw4 c4 (ℓ "亘") (ℓ "丶乜丷乜乢") tt tt Eq.refl

wl1271 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "亰亱义亱亰义") ⟫ʷ
wl1271 c4 = lw0 c4 (ℓ "京") (ℓ "亰亱义亱亰义") tt tt Eq.refl

wl1272 : Base 4 → ⟪ (ℓ "亐些") ⟫ʷ ≈ ⟪ (ℓ "些亐二") ⟫ʷ
wl1272 c4 = lw4 c4 (ℓ "亐些") (ℓ "些亐二") tt tt Eq.refl

wl1273 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "丨乜丩乜乇") ⟫ʷ
wl1273 c4 = lw4 c4 (ℓ "二") (ℓ "丨乜丩乜乇") tt tt Eq.refl

wl1274 : Base 4 → ⟪ (ℓ "亰並乤") ⟫ʷ ≈ ⟪ (ℓ "並亰") ⟫ʷ
wl1274 c4 = lw0 c4 (ℓ "亰並乤") (ℓ "並亰") tt tt Eq.refl

wl1275 : Base 4 → ⟪ (ℓ "乤亓") ⟫ʷ ≈ ⟪ (ℓ "亓乤二") ⟫ʷ
wl1275 c4 = lw4 c4 (ℓ "乤亓") (ℓ "亓乤二") tt tt Eq.refl

wl1276 : Base 4 → ⟪ (ℓ "並乤乤") ⟫ʷ ≈ ⟪ (ℓ "並") ⟫ʷ
wl1276 c4 = lw0 c4 (ℓ "並乤乤") (ℓ "並") tt tt Eq.refl

wl1277 : Base 4 → ⟪ (ℓ "京亲") ⟫ʷ ≈ ⟪ (ℓ "亲京亨") ⟫ʷ
wl1277 c4 = lw0 c4 (ℓ "京亲") (ℓ "亲京亨") tt tt Eq.refl

wl1278 : Base 4 → ⟪ (ℓ "亐些二") ⟫ʷ ≈ ⟪ (ℓ "些亐") ⟫ʷ
wl1278 c4 = lw4 c4 (ℓ "亐些二") (ℓ "些亐") tt tt Eq.refl

wl1279 : Base 4 → ⟪ (ℓ "京並乐") ⟫ʷ ≈ ⟪ (ℓ "並京") ⟫ʷ
wl1279 c4 = lw0 c4 (ℓ "京並乐") (ℓ "並京") tt tt Eq.refl

wl1280 : Base 4 → ⟪ (ℓ "乐些") ⟫ʷ ≈ ⟪ (ℓ "些乐二") ⟫ʷ
wl1280 c4 = lw4 c4 (ℓ "乐些") (ℓ "些乐二") tt tt Eq.refl

wl1281 : Base 4 → ⟪ (ℓ "京乐") ⟫ʷ ≈ ⟪ (ℓ "乐京") ⟫ʷ
wl1281 c4 = lw0 c4 (ℓ "京乐") (ℓ "乐京") tt tt Eq.refl

wl1282 : Base 4 → ⟪ (ℓ "並乐乐") ⟫ʷ ≈ ⟪ (ℓ "並") ⟫ʷ
wl1282 c4 = lw0 c4 (ℓ "並乐乐") (ℓ "並") tt tt Eq.refl

wl1283 : Base 4 → ⟪ (ℓ "亘亍") ⟫ʷ ≈ ⟪ (ℓ "亍亘交") ⟫ʷ
wl1283 c4 = lw4 c4 (ℓ "亘亍") (ℓ "亍亘交") tt tt Eq.refl

wl1284 : Base 4 → ⟪ (ℓ "乎亍") ⟫ʷ ≈ ⟪ (ℓ "亍乎") ⟫ʷ
wl1284 c4 = lw4 c4 (ℓ "乎亍") (ℓ "亍乎") tt tt Eq.refl

wl1285 : Base 4 → ⟪ (ℓ "亊亰亊丢亇亰亇丢") ⟫ʷ ≈ ⟪ (ℓ "亲亱") ⟫ʷ
wl1285 c4 = lw0 c4 (ℓ "亊亰亊丢亇亰亇丢") (ℓ "亲亱") tt tt Eq.refl

wl1286 : Base 4 → ⟪ (ℓ "交丢") ⟫ʷ ≈ ⟪ (ℓ "丢交") ⟫ʷ
wl1286 c4 = lw0 c4 (ℓ "交丢") (ℓ "丢交") tt tt Eq.refl

wl1287 : Base 4 → ⟪ (ℓ "亄亨亄丢亇亨亇丢") ⟫ʷ ≈ ⟪ (ℓ "亩亪") ⟫ʷ
wl1287 c4 = lw0 c4 (ℓ "亄亨亄丢亇亨亇丢") (ℓ "亩亪") tt tt Eq.refl

wl1288 : Base 4 → ⟪ (ℓ "亩亪亭乇亭么交亇亨亇丢亄亨亄交丢") ⟫ʷ ≈ ⟪ (ℓ "亲亱亲乎亲乏交亇亰亇丢亊亰亊交丢") ⟫ʷ
wl1288 c4 = lw0 c4 (ℓ "亩亪亭乇亭么交亇亨亇丢亄亨亄交丢") (ℓ "亲亱亲乎亲乏交亇亰亇丢亊亰亊交丢") tt tt Eq.refl

wl1289 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "亇亨亇丢亰亇亨亇丢亰") ⟫ʷ
wl1289 c4 = lw0 c4 (ℓ "京") (ℓ "亇亨亇丢亰亇亨亇丢亰") tt tt Eq.refl

wl1290 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "亄亨亄丢亇亨亇丢亰亇亨亇丢亄亨亄丢") ⟫ʷ
wl1290 c4 = lw0 c4 (ℓ "京") (ℓ "亄亨亄丢亇亨亇丢亰亇亨亇丢亄亨亄丢") tt tt Eq.refl

wl1291 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "京") ⟫ʷ
wl1291 c4 = lw0 c4 (ℓ "京") (ℓ "京") tt tt Eq.refl

wl1292 : Base 4 → ⟪ (ℓ "交亇交亰交亇交丢亨亨亨亲乎亨亨亲乏交交亇交交亰交交亇") ⟫ʷ ≈ ⟪ (ℓ "亇交亰交亇交丢亨亨亨亲乎亨亨亲乏交交亇交交亰交交亇交") ⟫ʷ
wl1292 c4 = lw0 c4 (ℓ "交亇交亰交亇交丢亨亨亨亲乎亨亨亲乏交交亇交交亰交交亇") (ℓ "亇交亰交亇交丢亨亨亨亲乎亨亨亲乏交交亇交交亰交交亇交") tt tt Eq.refl

wl1293 : Base 4 → ⟪ (ℓ "交丢亨亨亨亲乎亨亨亲乏") ⟫ʷ ≈ ⟪ (ℓ "丢亨亨亨亲乎亨亨亲乏交") ⟫ʷ
wl1293 c4 = lw0 c4 (ℓ "交丢亨亨亨亲乎亨亨亲乏") (ℓ "丢亨亨亨亲乎亨亨亲乏交") tt tt Eq.refl

wl1294 : Base 4 → ⟪ (ℓ "交亇交亨交亇交丢亰亰亰亭乇亰亰亭么交交亇交交亨交交亇") ⟫ʷ ≈ ⟪ (ℓ "亇交亨交亇交丢亰亰亰亭乇亰亰亭么交交亇交交亨交交亇交") ⟫ʷ
wl1294 c4 = lw0 c4 (ℓ "交亇交亨交亇交丢亰亰亰亭乇亰亰亭么交交亇交交亨交交亇") (ℓ "亇交亨交亇交丢亰亰亰亭乇亰亰亭么交交亇交交亨交交亇交") tt tt Eq.refl

wl1295 : Base 4 → ⟪ (ℓ "交丢亰亰亰亭乇亰亰亭么") ⟫ʷ ≈ ⟪ (ℓ "丢亰亰亰亭乇亰亰亭么交") ⟫ʷ
wl1295 c4 = lw0 c4 (ℓ "交丢亰亰亰亭乇亰亰亭么") (ℓ "丢亰亰亰亭乇亰亰亭么交") tt tt Eq.refl

wl1296 : Base 4 → ⟪ (ℓ "亭乇亭么亇亨亇丢亭乇亰亭么交亇亨亇交丢") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏亇亰亇丢亲乎亨亲乏交亇亰亇交丢") ⟫ʷ
wl1296 c4 = lw0 c4 (ℓ "亭乇亭么亇亨亇丢亭乇亰亭么交亇亨亇交丢") (ℓ "亲乎亲乏亇亰亇丢亲乎亨亲乏交亇亰亇交丢") tt tt Eq.refl

wl1297 : Base 4 → ⟪ (ℓ "交亰亰亭乇亰亰亭么") ⟫ʷ ≈ ⟪ (ℓ "亰亰亭乇亰亰亭么交") ⟫ʷ
wl1297 c4 = lw0 c4 (ℓ "交亰亰亭乇亰亰亭么") (ℓ "亰亰亭乇亰亰亭么交") tt tt Eq.refl

wl1298 : Base 4 → ⟪ (ℓ "乩亇亭乇亭么交亇交亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么交亇亭乇亭么交亇乩") ⟫ʷ
wl1298 c4 = lw0 c4 (ℓ "乩亇亭乇亭么交亇交亭乇亭么") (ℓ "亭乇亭么交亇亭乇亭么交亇乩") tt tt Eq.refl

wl1299 : Base 4 → ⟪ (ℓ "乹亊亭乇亭么交亊交亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么交亊亭乇亭么交亊乹") ⟫ʷ
wl1299 c4 = lw0 c4 (ℓ "乹亊亭乇亭么交亊交亭乇亭么") (ℓ "亭乇亭么交亊亭乇亭么交亊乹") tt tt Eq.refl

wl1300 : Base 4 → ⟪ (ℓ "乾乿") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1300 c4 = lw0 c4 (ℓ "乾乿") [] tt tt Eq.refl

wl1301 : Base 4 → ⟪ (ℓ "亇亨亇丢") ⟫ʷ ≈ ⟪ (ℓ "亪") ⟫ʷ
wl1301 c4 = lw0 c4 (ℓ "亇亨亇丢") (ℓ "亪") tt tt Eq.refl

wl1302 : Base 4 → ⟪ (ℓ "亄亨亄丢") ⟫ʷ ≈ ⟪ (ℓ "亩") ⟫ʷ
wl1302 c4 = lw0 c4 (ℓ "亄亨亄丢") (ℓ "亩") tt tt Eq.refl

wl1303 : Base 4 → ⟪ (ℓ "交亦乫亦交乫") ⟫ʷ ≈ ⟪ (ℓ "京") ⟫ʷ
wl1303 c4 = lw0 c4 (ℓ "交亦乫亦交乫") (ℓ "京") tt tt Eq.refl

wl1304 : Base 4 → ⟪ (ℓ "也些") ⟫ʷ ≈ ⟪ (ℓ "些也") ⟫ʷ
wl1304 c4 = lw4 c4 (ℓ "也些") (ℓ "些也") tt tt Eq.refl

wl1305 : Base 4 → ⟪ (ℓ "京也亰") ⟫ʷ ≈ ⟪ (ℓ "也京") ⟫ʷ
wl1305 c4 = lw0 c4 (ℓ "京也亰") (ℓ "也京") tt tt Eq.refl

wl1306 : Base 4 → ⟪ (ℓ "也亰亰") ⟫ʷ ≈ ⟪ (ℓ "也") ⟫ʷ
wl1306 c4 = lw0 c4 (ℓ "也亰亰") (ℓ "也") tt tt Eq.refl

wl1307 : Base 4 → ⟪ (ℓ "之些") ⟫ʷ ≈ ⟪ (ℓ "些之亓") ⟫ʷ
wl1307 c4 = lw4 c4 (ℓ "之些") (ℓ "些之亓") tt tt Eq.refl

wl1308 : Base 4 → ⟪ (ℓ "之亓亓") ⟫ʷ ≈ ⟪ (ℓ "之") ⟫ʷ
wl1308 c4 = lw4 c4 (ℓ "之亓亓") (ℓ "之") tt tt Eq.refl

wl1309 : Base 4 → ⟪ (ℓ "亩亲产") ⟫ʷ ≈ ⟪ (ℓ "产亩") ⟫ʷ
wl1309 c4 = lw0 c4 (ℓ "亩亲产") (ℓ "产亩") tt tt Eq.refl

wl1310 : Base 4 → ⟪ (ℓ "丒乩之乪之乕专") ⟫ʷ ≈ ⟪ (ℓ "亩") ⟫ʷ
wl1310 c4 = lw0 c4 (ℓ "丒乩之乪之乕专") (ℓ "亩") tt tt Eq.refl

wl1311 : Base 4 → ⟪ (ℓ "亩亲亲") ⟫ʷ ≈ ⟪ (ℓ "亩") ⟫ʷ
wl1311 c4 = lw0 c4 (ℓ "亩亲亲") (ℓ "亩") tt tt Eq.refl

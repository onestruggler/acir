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

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wp1123 : Base 4 → WsL → ⟪ (ℓ "二亄二五二亄二丢亨亝亨亨丨亝亨亨丩二二亄二二五二二亄") ⟫ʷ ≈ ⟪ (ℓ "亄二五二亄二丢亨亝亨亨丨亝亨亨丩二二亄二二五二二亄二") ⟫ʷ
wp1123 c4 L = pw3 c4 L (ℓ "二亄二五二亄二丢亨亝亨亨丨亝亨亨丩二二亄二二五二二亄") (ℓ "亄二五二亄二丢亨亝亨亨丨亝亨亨丩二二亄二二五二二亄二") tt tt Eq.refl

wp1124 : Base 4 → WsL → ⟪ (ℓ "二丢亨亝亨亨丨亝亨亨丩") ⟫ʷ ≈ ⟪ (ℓ "丢亨亝亨亨丨亝亨亨丩二") ⟫ʷ
wp1124 c4 L = pw3 c4 L (ℓ "二丢亨亝亨亨丨亝亨亨丩") (ℓ "丢亨亝亨亨丨亝亨亨丩二") tt tt Eq.refl

wp1125 : Base 4 → WsL → ⟪ (ℓ "亝丨亝丩亄五亄丢亝丨亝亨丩二亄五亄二丢") ⟫ʷ ≈ ⟪ (ℓ "亪丯亪丰亄亨亄丢亪丯亪五丰二亄亨亄二丢") ⟫ʷ
wp1125 c4 L = pw3 c4 L (ℓ "亝丨亝丩亄五亄丢亝丨亝亨丩二亄五亄二丢") (ℓ "亪丯亪丰亄亨亄丢亪丯亪五丰二亄亨亄二丢") tt tt Eq.refl

wp1126 : Base 4 → WsL → ⟪ (ℓ "乾亠") ⟫ʷ ≈ ⟪ (ℓ "亣乾") ⟫ʷ
wp1126 c4 L = pw1 c4 L (ℓ "乾亠") (ℓ "亣乾") tt tt Eq.refl

wp1127 : Base 4 → WsL → ⟪ (ℓ "亄五亄丢") ⟫ʷ ≈ ⟪ (ℓ "亖") ⟫ʷ
wp1127 c4 L = pw2 c4 L (ℓ "亄五亄丢") (ℓ "亖") tt tt Eq.refl

wp1128 : Base 4 → WsL → ⟪ (ℓ "亰些") ⟫ʷ ≈ ⟪ (ℓ "些亰亜") ⟫ʷ
wp1128 c4 L = pw1 c4 L (ℓ "亰些") (ℓ "些亰亜") tt tt Eq.refl

wp1129 : Base 4 → WsL → ⟪ (ℓ "京亓五") ⟫ʷ ≈ ⟪ (ℓ "亓京") ⟫ʷ
wp1129 c4 L = pw2 c4 L (ℓ "京亓五") (ℓ "亓京") tt tt Eq.refl

wp1130 : Base 4 → WsL → ⟪ (ℓ "亠丒") ⟫ʷ ≈ ⟪ (ℓ "丒亠") ⟫ʷ
wp1130 c4 L = pw2 c4 L (ℓ "亠丒") (ℓ "丒亠") tt tt Eq.refl

wp1131 : Base 4 → WsL → ⟪ (ℓ "亠专") ⟫ʷ ≈ ⟪ (ℓ "专亠") ⟫ʷ
wp1131 c4 L = pw2 c4 L (ℓ "亠专") (ℓ "专亠") tt tt Eq.refl

wp1132 : Base 4 → WsL → ⟪ (ℓ "丒乕丬乖丬丽专") ⟫ʷ ≈ ⟪ (ℓ "亖") ⟫ʷ
wp1132 c4 L = pw2 c4 L (ℓ "丒乕丬乖丬丽专") (ℓ "亖") tt tt Eq.refl

wp1133 : Base 4 → WsL → ⟪ (ℓ "京亖") ⟫ʷ ≈ ⟪ (ℓ "亖亠京") ⟫ʷ
wp1133 c4 L = pw2 c4 L (ℓ "京亖") (ℓ "亖亠京") tt tt Eq.refl

wp1134 : Base 4 → WsL → ⟪ (ℓ "亜亠些") ⟫ʷ ≈ ⟪ (ℓ "些亠") ⟫ʷ
wp1134 c4 L = pw1 c4 L (ℓ "亜亠些") (ℓ "些亠") tt tt Eq.refl

wp1135 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "亠亜亠") ⟫ʷ
wp1135 c4 L = pw1 c4 L (ℓ "亜") (ℓ "亠亜亠") tt tt Eq.refl

wp1136 : Base 4 → WsL → ⟪ (ℓ "亜亰些") ⟫ʷ ≈ ⟪ (ℓ "些亰") ⟫ʷ
wp1136 c4 L = pw1 c4 L (ℓ "亜亰些") (ℓ "些亰") tt tt Eq.refl

wp1137 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "亰亜亰") ⟫ʷ
wp1137 c4 L = pw1 c4 L (ℓ "亜") (ℓ "亰亜亰") tt tt Eq.refl

wp1138 : Base 4 → WsL → ⟪ (ℓ "亜些") ⟫ʷ ≈ ⟪ (ℓ "些亜") ⟫ʷ
wp1138 c4 L = pw1 c4 L (ℓ "亜些") (ℓ "些亜") tt tt Eq.refl

wp1139 : Base 4 → WsL → ⟪ (ℓ "亜亨亝亨亨丨亝亨亨丩亖") ⟫ʷ ≈ ⟪ (ℓ "亨亝亨亨丨亝亨亨丩亖亜") ⟫ʷ
wp1139 c4 L = pw3 c4 L (ℓ "亜亨亝亨亨丨亝亨亨丩亖") (ℓ "亨亝亨亨丨亝亨亨丩亖亜") tt tt Eq.refl

wp1140 : Base 4 → WsL → ⟪ (ℓ "亝丨亝丩亖亝丨亝亨丩亖亜亪亩亪亪丯亪丰亪五亩亜亪五") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp1140 c4 L = pw3 c4 L (ℓ "亝丨亝丩亖亝丨亝亨丩亖亜亪亩亪亪丯亪丰亪五亩亜亪五") [] tt tt Eq.refl

wp1141 : Base 4 → WsL → ⟪ (ℓ "丳亲") ⟫ʷ ≈ ⟪ (ℓ "亲丳亢") ⟫ʷ
wp1141 c4 L = pw1 c4 L (ℓ "丳亲") (ℓ "亲丳亢") tt tt Eq.refl

wp1142 : Base 4 → WsL → ⟪ (ℓ "亐亢五") ⟫ʷ ≈ ⟪ (ℓ "亢亐") ⟫ʷ
wp1142 c4 L = pw2 c4 L (ℓ "亐亢五") (ℓ "亢亐") tt tt Eq.refl

wp1143 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "丨亀丩亀乕") ⟫ʷ
wp1143 c4 L = pw2 c4 L (ℓ "五") (ℓ "丨亀丩亀乕") tt tt Eq.refl

wp1144 : Base 4 → WsL → ⟪ (ℓ "亢亲") ⟫ʷ ≈ ⟪ (ℓ "亲亢") ⟫ʷ
wp1144 c4 L = pw1 c4 L (ℓ "亢亲") (ℓ "亲亢") tt tt Eq.refl

wp1145 : Base 4 → WsL → ⟪ (ℓ "丳亢亢") ⟫ʷ ≈ ⟪ (ℓ "丳") ⟫ʷ
wp1145 c4 L = pw1 c4 L (ℓ "丳亢亢") (ℓ "丳") tt tt Eq.refl

wp1146 : Base 4 → WsL → ⟪ (ℓ "亠串") ⟫ʷ ≈ ⟪ (ℓ "串亰") ⟫ʷ
wp1146 c4 L = pw1 c4 L (ℓ "亠串") (ℓ "串亰") tt tt Eq.refl

wp1147 : Base 4 → WsL → ⟪ (ℓ "串亲") ⟫ʷ ≈ ⟪ (ℓ "亢串") ⟫ʷ
wp1147 c4 L = pw1 c4 L (ℓ "串亲") (ℓ "亢串") tt tt Eq.refl

wp1148 : Base 4 → WsL → ⟪ (ℓ "亰串") ⟫ʷ ≈ ⟪ (ℓ "串亠") ⟫ʷ
wp1148 c4 L = pw1 c4 L (ℓ "亰串") (ℓ "串亠") tt tt Eq.refl

wp1149 : Base 4 → WsL → ⟪ (ℓ "串亣") ⟫ʷ ≈ ⟪ (ℓ "亳串") ⟫ʷ
wp1149 c4 L = pw1 c4 L (ℓ "串亣") (ℓ "亳串") tt tt Eq.refl

wp1150 : Base 4 → WsL → ⟪ (ℓ "二亞") ⟫ʷ ≈ ⟪ (ℓ "亞二五") ⟫ʷ
wp1150 c4 L = pw3 c4 L (ℓ "二亞") (ℓ "亞二五") tt tt Eq.refl

wp1151 : Base 4 → WsL → ⟪ (ℓ "买亞") ⟫ʷ ≈ ⟪ (ℓ "亞买亱") ⟫ʷ
wp1151 c4 L = pw1 c4 L (ℓ "买亞") (ℓ "亞买亱") tt tt Eq.refl

wp1152 : Base 4 → WsL → ⟪ (ℓ "乕亞") ⟫ʷ ≈ ⟪ (ℓ "亞乕") ⟫ʷ
wp1152 c4 L = pw3 c4 L (ℓ "乕亞") (ℓ "亞乕") tt tt Eq.refl

wp1153 : Base 4 → WsL → ⟪ (ℓ "亞亱") ⟫ʷ ≈ ⟪ (ℓ "亱亞") ⟫ʷ
wp1153 c4 L = pw1 c4 L (ℓ "亞亱") (ℓ "亱亞") tt tt Eq.refl

wp1154 : Base 4 → WsL → ⟪ (ℓ "买亱亱") ⟫ʷ ≈ ⟪ (ℓ "买") ⟫ʷ
wp1154 c4 L = pw1 c4 L (ℓ "买亱亱") (ℓ "买") tt tt Eq.refl

wp1155 : Base 4 → WsL → ⟪ (ℓ "亰丹") ⟫ʷ ≈ ⟪ (ℓ "丹亜") ⟫ʷ
wp1155 c4 L = pw1 c4 L (ℓ "亰丹") (ℓ "丹亜") tt tt Eq.refl

wp1156 : Base 4 → WsL → ⟪ (ℓ "丹亞") ⟫ʷ ≈ ⟪ (ℓ "亱丹") ⟫ʷ
wp1156 c4 L = pw1 c4 L (ℓ "丹亞") (ℓ "亱丹") tt tt Eq.refl

wp1157 : Base 4 → WsL → ⟪ (ℓ "亜丹") ⟫ʷ ≈ ⟪ (ℓ "丹亰") ⟫ʷ
wp1157 c4 L = pw1 c4 L (ℓ "亜丹") (ℓ "丹亰") tt tt Eq.refl

wp1158 : Base 4 → WsL → ⟪ (ℓ "丹亳") ⟫ʷ ≈ ⟪ (ℓ "亟丹") ⟫ʷ
wp1158 c4 L = pw1 c4 L (ℓ "丹亳") (ℓ "亟丹") tt tt Eq.refl

wp1159 : Base 4 → WsL → ⟪ (ℓ "亐亢") ⟫ʷ ≈ ⟪ (ℓ "亢亐五") ⟫ʷ
wp1159 c4 L = pw2 c4 L (ℓ "亐亢") (ℓ "亢亐五") tt tt Eq.refl

wp1160 : Base 4 → WsL → ⟪ (ℓ "乜亢") ⟫ʷ ≈ ⟪ (ℓ "亢乜亲") ⟫ʷ
wp1160 c4 L = pw1 c4 L (ℓ "乜亢") (ℓ "亢乜亲") tt tt Eq.refl

wp1161 : Base 4 → WsL → ⟪ (ℓ "乜亲亲") ⟫ʷ ≈ ⟪ (ℓ "乜") ⟫ʷ
wp1161 c4 L = pw1 c4 L (ℓ "乜亲亲") (ℓ "乜") tt tt Eq.refl

wp1162 : Base 4 → WsL → ⟪ (ℓ "串亢") ⟫ʷ ≈ ⟪ (ℓ "亲串") ⟫ʷ
wp1162 c4 L = pw1 c4 L (ℓ "串亢") (ℓ "亲串") tt tt Eq.refl

wp1163 : Base 4 → WsL → ⟪ (ℓ "串亳") ⟫ʷ ≈ ⟪ (ℓ "亣串") ⟫ʷ
wp1163 c4 L = pw1 c4 L (ℓ "串亳") (ℓ "亣串") tt tt Eq.refl

wp1164 : Base 4 → WsL → ⟪ (ℓ "乙亏") ⟫ʷ ≈ ⟪ (ℓ "亏乙") ⟫ʷ
wp1164 c4 L = pw3 c4 L (ℓ "乙亏") (ℓ "亏乙") tt tt Eq.refl

wp1165 : Base 4 → WsL → ⟪ (ℓ "亃亏") ⟫ʷ ≈ ⟪ (ℓ "亏亃亞") ⟫ʷ
wp1165 c4 L = pw3 c4 L (ℓ "亃亏") (ℓ "亏亃亞") tt tt Eq.refl

wp1166 : Base 4 → WsL → ⟪ (ℓ "亰亞亠") ⟫ʷ ≈ ⟪ (ℓ "亞亰") ⟫ʷ
wp1166 c4 L = pw1 c4 L (ℓ "亰亞亠") (ℓ "亞亰") tt tt Eq.refl

wp1167 : Base 4 → WsL → ⟪ (ℓ "乁亏") ⟫ʷ ≈ ⟪ (ℓ "亏乁") ⟫ʷ
wp1167 c4 L = pw3 c4 L (ℓ "乁亏") (ℓ "亏乁") tt tt Eq.refl

wp1168 : Base 4 → WsL → ⟪ (ℓ "亃亞亞") ⟫ʷ ≈ ⟪ (ℓ "亃") ⟫ʷ
wp1168 c4 L = pw3 c4 L (ℓ "亃亞亞") (ℓ "亃") tt tt Eq.refl

wp1169 : Base 4 → WsL → ⟪ (ℓ "丘丽乭举乭丯丙") ⟫ʷ ≈ ⟪ (ℓ "亞") ⟫ʷ
wp1169 c4 L = pw1 c4 L (ℓ "丘丽乭举乭丯丙") (ℓ "亞") tt tt Eq.refl

wp1170 : Base 4 → WsL → ⟪ (ℓ "举亓") ⟫ʷ ≈ ⟪ (ℓ "亓举") ⟫ʷ
wp1170 c4 L = pw2 c4 L (ℓ "举亓") (ℓ "亓举") tt tt Eq.refl

wp1171 : Base 4 → WsL → ⟪ (ℓ "亰亀") ⟫ʷ ≈ ⟪ (ℓ "亀亰") ⟫ʷ
wp1171 c4 L = pw1 c4 L (ℓ "亰亀") (ℓ "亀亰") tt tt Eq.refl

wp1172 : Base 4 → WsL → ⟪ (ℓ "亞亠亠") ⟫ʷ ≈ ⟪ (ℓ "亞") ⟫ʷ
wp1172 c4 L = pw1 c4 L (ℓ "亞亠亠") (ℓ "亞") tt tt Eq.refl

wp1173 : Base 4 → WsL → ⟪ (ℓ "五亓") ⟫ʷ ≈ ⟪ (ℓ "亓五") ⟫ʷ
wp1173 c4 L = pw2 c4 L (ℓ "五亓") (ℓ "亓五") tt tt Eq.refl

wp1174 : Base 4 → WsL → ⟪ (ℓ "五亞") ⟫ʷ ≈ ⟪ (ℓ "亞五") ⟫ʷ
wp1174 c4 L = pw3 c4 L (ℓ "五亞") (ℓ "亞五") tt tt Eq.refl

wp1175 : Base 4 → WsL → ⟪ (ℓ "买亱") ⟫ʷ ≈ ⟪ (ℓ "亱买") ⟫ʷ
wp1175 c4 L = pw1 c4 L (ℓ "买亱") (ℓ "亱买") tt tt Eq.refl

wp1176 : Base 4 → WsL → ⟪ (ℓ "为亱") ⟫ʷ ≈ ⟪ (ℓ "亱为亞") ⟫ʷ
wp1176 c4 L = pw1 c4 L (ℓ "为亱") (ℓ "亱为亞") tt tt Eq.refl

wp1177 : Base 4 → WsL → ⟪ (ℓ "二亞五") ⟫ʷ ≈ ⟪ (ℓ "亞二") ⟫ʷ
wp1177 c4 L = pw3 c4 L (ℓ "二亞五") (ℓ "亞二") tt tt Eq.refl

wp1178 : Base 4 → WsL → ⟪ (ℓ "亀亱") ⟫ʷ ≈ ⟪ (ℓ "亱亀") ⟫ʷ
wp1178 c4 L = pw1 c4 L (ℓ "亀亱") (ℓ "亱亀") tt tt Eq.refl

wp1179 : Base 4 → WsL → ⟪ (ℓ "为亞亞") ⟫ʷ ≈ ⟪ (ℓ "为") ⟫ʷ
wp1179 c4 L = pw1 c4 L (ℓ "为亞亞") (ℓ "为") tt tt Eq.refl

wp1180 : Base 4 → WsL → ⟪ (ℓ "丹亱") ⟫ʷ ≈ ⟪ (ℓ "亞丹") ⟫ʷ
wp1180 c4 L = pw1 c4 L (ℓ "丹亱") (ℓ "亞丹") tt tt Eq.refl

wp1181 : Base 4 → WsL → ⟪ (ℓ "丹亟") ⟫ʷ ≈ ⟪ (ℓ "亳丹") ⟫ʷ
wp1181 c4 L = pw1 c4 L (ℓ "丹亟") (ℓ "亳丹") tt tt Eq.refl

wp1182 : Base 4 → WsL → ⟪ (ℓ "亱亢") ⟫ʷ ≈ ⟪ (ℓ "亢亞亱") ⟫ʷ
wp1182 c4 L = pw1 c4 L (ℓ "亱亢") (ℓ "亢亞亱") tt tt Eq.refl

wp1183 : Base 4 → WsL → ⟪ (ℓ "乖亞") ⟫ʷ ≈ ⟪ (ℓ "亞乖") ⟫ʷ
wp1183 c4 L = pw3 c4 L (ℓ "乖亞") (ℓ "亞乖") tt tt Eq.refl

wp1184 : Base 4 → WsL → ⟪ (ℓ "亞亢") ⟫ʷ ≈ ⟪ (ℓ "亢亞") ⟫ʷ
wp1184 c4 L = pw1 c4 L (ℓ "亞亢") (ℓ "亢亞") tt tt Eq.refl

wp1185 : Base 4 → WsL → ⟪ (ℓ "丞丽乽举乽丶丟") ⟫ʷ ≈ ⟪ (ℓ "亢") ⟫ʷ
wp1185 c4 L = pw1 c4 L (ℓ "丞丽乽举乽丶丟") (ℓ "亢") tt tt Eq.refl

wp1186 : Base 4 → WsL → ⟪ (ℓ "举亏") ⟫ʷ ≈ ⟪ (ℓ "亏举") ⟫ʷ
wp1186 c4 L = pw3 c4 L (ℓ "举亏") (ℓ "亏举") tt tt Eq.refl

wp1187 : Base 4 → WsL → ⟪ (ℓ "丽亏") ⟫ʷ ≈ ⟪ (ℓ "亏丽") ⟫ʷ
wp1187 c4 L = pw3 c4 L (ℓ "丽亏") (ℓ "亏丽") tt tt Eq.refl

wp1188 : Base 4 → WsL → ⟪ (ℓ "亢亜亜") ⟫ʷ ≈ ⟪ (ℓ "亢") ⟫ʷ
wp1188 c4 L = pw1 c4 L (ℓ "亢亜亜") (ℓ "亢") tt tt Eq.refl

wp1189 : Base 4 → WsL → ⟪ (ℓ "五亏") ⟫ʷ ≈ ⟪ (ℓ "亏五") ⟫ʷ
wp1189 c4 L = pw3 c4 L (ℓ "五亏") (ℓ "亏五") tt tt Eq.refl

wp1190 : Base 4 → WsL → ⟪ (ℓ "亜乄亨") ⟫ʷ ≈ ⟪ (ℓ "乄亜") ⟫ʷ
wp1190 c4 L = pw3 c4 L (ℓ "亜乄亨") (ℓ "乄亜") tt tt Eq.refl

wp1191 : Base 4 → WsL → ⟪ (ℓ "乄亨亨") ⟫ʷ ≈ ⟪ (ℓ "乄") ⟫ʷ
wp1191 c4 L = pw3 c4 L (ℓ "乄亨亨") (ℓ "乄") tt tt Eq.refl

wp1192 : Base 4 → WsL → ⟪ (ℓ "亜亚亠") ⟫ʷ ≈ ⟪ (ℓ "亚亜") ⟫ʷ
wp1192 c4 L = pw1 c4 L (ℓ "亜亚亠") (ℓ "亚亜") tt tt Eq.refl

wp1193 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "丽买举买乹") ⟫ʷ
wp1193 c4 L = pw1 c4 L (ℓ "亠") (ℓ "丽买举买乹") tt tt Eq.refl

wp1194 : Base 4 → WsL → ⟪ (ℓ "二亪") ⟫ʷ ≈ ⟪ (ℓ "亪二五") ⟫ʷ
wp1194 c4 L = pw3 c4 L (ℓ "二亪") (ℓ "亪二五") tt tt Eq.refl

wp1195 : Base 4 → WsL → ⟪ (ℓ "丩亪") ⟫ʷ ≈ ⟪ (ℓ "亪丩") ⟫ʷ
wp1195 c4 L = pw3 c4 L (ℓ "丩亪") (ℓ "亪丩") tt tt Eq.refl

wp1196 : Base 4 → WsL → ⟪ (ℓ "亨丬亜") ⟫ʷ ≈ ⟪ (ℓ "丬亨") ⟫ʷ
wp1196 c4 L = pw3 c4 L (ℓ "亨丬亜") (ℓ "丬亨") tt tt Eq.refl

wp1197 : Base 4 → WsL → ⟪ (ℓ "亜亚") ⟫ʷ ≈ ⟪ (ℓ "亚亜亠") ⟫ʷ
wp1197 c4 L = pw1 c4 L (ℓ "亜亚") (ℓ "亚亜亠") tt tt Eq.refl

wp1198 : Base 4 → WsL → ⟪ (ℓ "丬亜亜") ⟫ʷ ≈ ⟪ (ℓ "丬") ⟫ʷ
wp1198 c4 L = pw3 c4 L (ℓ "丬亜亜") (ℓ "丬") tt tt Eq.refl

wp1199 : Base 4 → WsL → ⟪ (ℓ "乹亚") ⟫ʷ ≈ ⟪ (ℓ "亚乹") ⟫ʷ
wp1199 c4 L = pw1 c4 L (ℓ "乹亚") (ℓ "亚乹") tt tt Eq.refl

wp1200 : Base 4 → WsL → ⟪ (ℓ "亞亢亲") ⟫ʷ ≈ ⟪ (ℓ "亲亞") ⟫ʷ
wp1200 c4 L = pw1 c4 L (ℓ "亞亢亲") (ℓ "亲亞") tt tt Eq.refl

wp1201 : Base 4 → WsL → ⟪ (ℓ "乖亢") ⟫ʷ ≈ ⟪ (ℓ "亢乖") ⟫ʷ
wp1201 c4 L = pw2 c4 L (ℓ "乖亢") (ℓ "亢乖") tt tt Eq.refl

wp1202 : Base 4 → WsL → ⟪ (ℓ "亠些亜") ⟫ʷ ≈ ⟪ (ℓ "些亠") ⟫ʷ
wp1202 c4 L = pw1 c4 L (ℓ "亠些亜") (ℓ "些亠") tt tt Eq.refl

wp1203 : Base 4 → WsL → ⟪ (ℓ "丩亮") ⟫ʷ ≈ ⟪ (ℓ "亮丩") ⟫ʷ
wp1203 c4 L = pw2 c4 L (ℓ "丩亮") (ℓ "亮丩") tt tt Eq.refl

wp1204 : Base 4 → WsL → ⟪ (ℓ "京丬亠") ⟫ʷ ≈ ⟪ (ℓ "丬京") ⟫ʷ
wp1204 c4 L = pw2 c4 L (ℓ "京丬亠") (ℓ "丬京") tt tt Eq.refl

wp1205 : Base 4 → WsL → ⟪ (ℓ "亠些") ⟫ʷ ≈ ⟪ (ℓ "些亠亜") ⟫ʷ
wp1205 c4 L = pw1 c4 L (ℓ "亠些") (ℓ "些亠亜") tt tt Eq.refl

wp1206 : Base 4 → WsL → ⟪ (ℓ "京举") ⟫ʷ ≈ ⟪ (ℓ "举京") ⟫ʷ
wp1206 c4 L = pw2 c4 L (ℓ "京举") (ℓ "举京") tt tt Eq.refl

wp1207 : Base 4 → WsL → ⟪ (ℓ "丬亠亠") ⟫ʷ ≈ ⟪ (ℓ "丬") ⟫ʷ
wp1207 c4 L = pw2 c4 L (ℓ "丬亠亠") (ℓ "丬") tt tt Eq.refl

wp1208 : Base 4 → WsL → ⟪ (ℓ "亙亱") ⟫ʷ ≈ ⟪ (ℓ "亡亱亙") ⟫ʷ
wp1208 c4 L = pw1 c4 L (ℓ "亙亱") (ℓ "亡亱亙") tt tt Eq.refl

wp1209 : Base 4 → WsL → ⟪ (ℓ "五亡") ⟫ʷ ≈ ⟪ (ℓ "亡京五") ⟫ʷ
wp1209 c4 L = pw2 c4 L (ℓ "五亡") (ℓ "亡京五") tt tt Eq.refl

wp1210 : Base 4 → WsL → ⟪ (ℓ "五丘") ⟫ʷ ≈ ⟪ (ℓ "丘五") ⟫ʷ
wp1210 c4 L = pw3 c4 L (ℓ "五丘") (ℓ "丘五") tt tt Eq.refl

wp1211 : Base 4 → WsL → ⟪ (ℓ "五丙") ⟫ʷ ≈ ⟪ (ℓ "丙五") ⟫ʷ
wp1211 c4 L = pw3 c4 L (ℓ "五丙") (ℓ "丙五") tt tt Eq.refl

wp1212 : Base 4 → WsL → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "亡京亡") ⟫ʷ
wp1212 c4 L = pw2 c4 L (ℓ "京") (ℓ "亡京亡") tt tt Eq.refl

wp1213 : Base 4 → WsL → ⟪ (ℓ "五京云") ⟫ʷ ≈ ⟪ (ℓ "云五") ⟫ʷ
wp1213 c4 L = pw2 c4 L (ℓ "五京云") (ℓ "云五") tt tt Eq.refl

wp1214 : Base 4 → WsL → ⟪ (ℓ "亠京云") ⟫ʷ ≈ ⟪ (ℓ "云亠") ⟫ʷ
wp1214 c4 L = pw2 c4 L (ℓ "亠京云") (ℓ "云亠") tt tt Eq.refl

wp1215 : Base 4 → WsL → ⟪ (ℓ "亱亠亠") ⟫ʷ ≈ ⟪ (ℓ "亱") ⟫ʷ
wp1215 c4 L = pw1 c4 L (ℓ "亱亠亠") (ℓ "亱") tt tt Eq.refl

wp1216 : Base 4 → WsL → ⟪ (ℓ "亁亠") ⟫ʷ ≈ ⟪ (ℓ "亡亁") ⟫ʷ
wp1216 c4 L = pw1 c4 L (ℓ "亁亠") (ℓ "亡亁") tt tt Eq.refl

wp1217 : Base 4 → WsL → ⟪ (ℓ "亁亂") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp1217 c4 L = pw1 c4 L (ℓ "亁亂") [] tt tt Eq.refl

wp1218 : Base 4 → WsL → ⟪ (ℓ "亁丢") ⟫ʷ ≈ ⟪ (ℓ "亂") ⟫ʷ
wp1218 c4 L = pw1 c4 L (ℓ "亁丢") (ℓ "亂") tt tt Eq.refl

wp1219 : Base 4 → WsL → ⟪ (ℓ "亰亠亞") ⟫ʷ ≈ ⟪ (ℓ "亞亰") ⟫ʷ
wp1219 c4 L = pw1 c4 L (ℓ "亰亠亞") (ℓ "亞亰") tt tt Eq.refl

wp1220 : Base 4 → WsL → ⟪ (ℓ "丟亞") ⟫ʷ ≈ ⟪ (ℓ "亞丟") ⟫ʷ
wp1220 c4 L = pw1 c4 L (ℓ "丟亞") (ℓ "亞丟") tt tt Eq.refl

wp1221 : Base 4 → WsL → ⟪ (ℓ "丩亞") ⟫ʷ ≈ ⟪ (ℓ "亞丩") ⟫ʷ
wp1221 c4 L = pw3 c4 L (ℓ "丩亞") (ℓ "亞丩") tt tt Eq.refl

wp1222 : Base 4 → WsL → ⟪ (ℓ "丞亞") ⟫ʷ ≈ ⟪ (ℓ "亞丞") ⟫ʷ
wp1222 c4 L = pw1 c4 L (ℓ "丞亞") (ℓ "亞丞") tt tt Eq.refl

wp1223 : Base 4 → WsL → ⟪ (ℓ "亨亏") ⟫ʷ ≈ ⟪ (ℓ "亏亨五") ⟫ʷ
wp1223 c4 L = pw3 c4 L (ℓ "亨亏") (ℓ "亏亨五") tt tt Eq.refl

wp1224 : Base 4 → WsL → ⟪ (ℓ "乖亓") ⟫ʷ ≈ ⟪ (ℓ "亓乖") ⟫ʷ
wp1224 c4 L = pw2 c4 L (ℓ "乖亓") (ℓ "亓乖") tt tt Eq.refl

wp1225 : Base 4 → WsL → ⟪ (ℓ "丩亢") ⟫ʷ ≈ ⟪ (ℓ "亢丩") ⟫ʷ
wp1225 c4 L = pw2 c4 L (ℓ "丩亢") (ℓ "亢丩") tt tt Eq.refl

wp1226 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "乒五乒") ⟫ʷ
wp1226 c4 L = pw2 c4 L (ℓ "五") (ℓ "乒五乒") tt tt Eq.refl

wp1227 : Base 4 → WsL → ⟪ (ℓ "亰亚亠") ⟫ʷ ≈ ⟪ (ℓ "亚亰") ⟫ʷ
wp1227 c4 L = pw1 c4 L (ℓ "亰亚亠") (ℓ "亚亰") tt tt Eq.refl

wp1228 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "乳亠乳") ⟫ʷ
wp1228 c4 L = pw2 c4 L (ℓ "亠") (ℓ "乳亠乳") tt tt Eq.refl

wp1229 : Base 4 → WsL → ⟪ (ℓ "五乳") ⟫ʷ ≈ ⟪ (ℓ "乳亠五") ⟫ʷ
wp1229 c4 L = pw2 c4 L (ℓ "五乳") (ℓ "乳亠五") tt tt Eq.refl

wp1230 : Base 4 → WsL → ⟪ (ℓ "亠乒") ⟫ʷ ≈ ⟪ (ℓ "乒五亠") ⟫ʷ
wp1230 c4 L = pw2 c4 L (ℓ "亠乒") (ℓ "乒五亠") tt tt Eq.refl

wp1231 : Base 4 → WsL → ⟪ (ℓ "五亠五亠五") ⟫ʷ ≈ ⟪ (ℓ "五") ⟫ʷ
wp1231 c4 L = pw2 c4 L (ℓ "五亠五亠五") (ℓ "五") tt tt Eq.refl

wp1232 : Base 4 → WsL → ⟪ (ℓ "二亍丿亍二丿") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
wp1232 c4 L = pw3 c4 L (ℓ "二亍丿亍二丿") (ℓ "亨") tt tt Eq.refl

wp1233 : Base 4 → WsL → ⟪ (ℓ "二井") ⟫ʷ ≈ ⟪ (ℓ "井二亨") ⟫ʷ
wp1233 c4 L = pw3 c4 L (ℓ "二井") (ℓ "井二亨") tt tt Eq.refl

wp1234 : Base 4 → WsL → ⟪ (ℓ "乳井") ⟫ʷ ≈ ⟪ (ℓ "井乳亡") ⟫ʷ
wp1234 c4 L = pw2 c4 L (ℓ "乳井") (ℓ "井乳亡") tt tt Eq.refl

wp1235 : Base 4 → WsL → ⟪ (ℓ "亘亡亰") ⟫ʷ ≈ ⟪ (ℓ "亡亘") ⟫ʷ
wp1235 c4 L = pw1 c4 L (ℓ "亘亡亰") (ℓ "亡亘") tt tt Eq.refl

wp1236 : Base 4 → WsL → ⟪ (ℓ "乳亡亡") ⟫ʷ ≈ ⟪ (ℓ "乳") ⟫ʷ
wp1236 c4 L = pw2 c4 L (ℓ "乳亡亡") (ℓ "乳") tt tt Eq.refl

wp1237 : Base 4 → WsL → ⟪ (ℓ "乑井") ⟫ʷ ≈ ⟪ (ℓ "亡乑") ⟫ʷ
wp1237 c4 L = pw2 c4 L (ℓ "乑井") (ℓ "亡乑") tt tt Eq.refl

wp1238 : Base 4 → WsL → ⟪ (ℓ "乑亣") ⟫ʷ ≈ ⟪ (ℓ "亗乑") ⟫ʷ
wp1238 c4 L = pw2 c4 L (ℓ "乑亣") (ℓ "亗乑") tt tt Eq.refl

wp1239 : Base 4 → WsL → ⟪ (ℓ "丌乕乁乖乁丨不") ⟫ʷ ≈ ⟪ (ℓ "井") ⟫ʷ
wp1239 c4 L = pw2 c4 L (ℓ "丌乕乁乖乁丨不") (ℓ "井") tt tt Eq.refl

wp1240 : Base 4 → WsL → ⟪ (ℓ "井京京") ⟫ʷ ≈ ⟪ (ℓ "井") ⟫ʷ
wp1240 c4 L = pw2 c4 L (ℓ "井京京") (ℓ "井") tt tt Eq.refl

wp1241 : Base 4 → WsL → ⟪ (ℓ "亡亮") ⟫ʷ ≈ ⟪ (ℓ "亮井亡") ⟫ʷ
wp1241 c4 L = pw2 c4 L (ℓ "亡亮") (ℓ "亮井亡") tt tt Eq.refl

wp1242 : Base 4 → WsL → ⟪ (ℓ "亘亰亡") ⟫ʷ ≈ ⟪ (ℓ "亡亘") ⟫ʷ
wp1242 c4 L = pw1 c4 L (ℓ "亘亰亡") (ℓ "亡亘") tt tt Eq.refl

wp1243 : Base 4 → WsL → ⟪ (ℓ "亘亰") ⟫ʷ ≈ ⟪ (ℓ "亡亘亡") ⟫ʷ
wp1243 c4 L = pw1 c4 L (ℓ "亘亰") (ℓ "亡亘亡") tt tt Eq.refl

wp1244 : Base 4 → WsL → ⟪ (ℓ "乪井") ⟫ʷ ≈ ⟪ (ℓ "井乪") ⟫ʷ
wp1244 c4 L = pw3 c4 L (ℓ "乪井") (ℓ "井乪") tt tt Eq.refl

wp1245 : Base 4 → WsL → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "亰亘亰") ⟫ʷ
wp1245 c4 L = pw1 c4 L (ℓ "亘") (ℓ "亰亘亰") tt tt Eq.refl

wp1246 : Base 4 → WsL → ⟪ (ℓ "井亮") ⟫ʷ ≈ ⟪ (ℓ "亮井") ⟫ʷ
wp1246 c4 L = pw2 c4 L (ℓ "井亮") (ℓ "亮井") tt tt Eq.refl

wp1247 : Base 4 → WsL → ⟪ (ℓ "乖亍") ⟫ʷ ≈ ⟪ (ℓ "亍乖") ⟫ʷ
wp1247 c4 L = pw3 c4 L (ℓ "乖亍") (ℓ "亍乖") tt tt Eq.refl

wp1248 : Base 4 → WsL → ⟪ (ℓ "亮五五") ⟫ʷ ≈ ⟪ (ℓ "亮") ⟫ʷ
wp1248 c4 L = pw2 c4 L (ℓ "亮五五") (ℓ "亮") tt tt Eq.refl

wp1249 : Base 4 → WsL → ⟪ (ℓ "亰亚") ⟫ʷ ≈ ⟪ (ℓ "亚亰亠") ⟫ʷ
wp1249 c4 L = pw1 c4 L (ℓ "亰亚") (ℓ "亚亰亠") tt tt Eq.refl

wp1250 : Base 4 → WsL → ⟪ (ℓ "亨亏五") ⟫ʷ ≈ ⟪ (ℓ "亏亨") ⟫ʷ
wp1250 c4 L = pw3 c4 L (ℓ "亨亏五") (ℓ "亏亨") tt tt Eq.refl

wp1251 : Base 4 → WsL → ⟪ (ℓ "丽亚") ⟫ʷ ≈ ⟪ (ℓ "亚丽") ⟫ʷ
wp1251 c4 L = pw1 c4 L (ℓ "丽亚") (ℓ "亚丽") tt tt Eq.refl

wp1252 : Base 4 → WsL → ⟪ (ℓ "亠五亠五亠") ⟫ʷ ≈ ⟪ (ℓ "亠") ⟫ʷ
wp1252 c4 L = pw2 c4 L (ℓ "亠五亠五亠") (ℓ "亠") tt tt Eq.refl

wp1253 : Base 4 → WsL → ⟪ (ℓ "丌乹为乺为丽不") ⟫ʷ ≈ ⟪ (ℓ "亡") ⟫ʷ
wp1253 c4 L = pw1 c4 L (ℓ "丌乹为乺为丽不") (ℓ "亡") tt tt Eq.refl

wp1254 : Base 4 → WsL → ⟪ (ℓ "亘亡") ⟫ʷ ≈ ⟪ (ℓ "亡亰亘") ⟫ʷ
wp1254 c4 L = pw1 c4 L (ℓ "亘亡") (ℓ "亡亰亘") tt tt Eq.refl

wp1255 : Base 4 → WsL → ⟪ (ℓ "五亍") ⟫ʷ ≈ ⟪ (ℓ "亍亨五") ⟫ʷ
wp1255 c4 L = pw3 c4 L (ℓ "五亍") (ℓ "亍亨五") tt tt Eq.refl

wp1256 : Base 4 → WsL → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "亍亨亍") ⟫ʷ
wp1256 c4 L = pw3 c4 L (ℓ "亨") (ℓ "亍亨亍") tt tt Eq.refl

wp1257 : Base 4 → WsL → ⟪ (ℓ "京亡京") ⟫ʷ ≈ ⟪ (ℓ "亡") ⟫ʷ
wp1257 c4 L = pw2 c4 L (ℓ "京亡京") (ℓ "亡") tt tt Eq.refl

wp1258 : Base 4 → WsL → ⟪ (ℓ "亂亁") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp1258 c4 L = pw1 c4 L (ℓ "亂亁") [] tt tt Eq.refl

wp1259 : Base 4 → WsL → ⟪ (ℓ "亐丨亐五亮丶") ⟫ʷ ≈ ⟪ (ℓ "亮丶丨五") ⟫ʷ
wp1259 c4 L = pw2 c4 L (ℓ "亐丨亐五亮丶") (ℓ "亮丶丨五") tt tt Eq.refl

wp1260 : Base 4 → WsL → ⟪ (ℓ "五亮丶丨五") ⟫ʷ ≈ ⟪ (ℓ "亮丶丨") ⟫ʷ
wp1260 c4 L = pw2 c4 L (ℓ "五亮丶丨五") (ℓ "亮丶丨") tt tt Eq.refl

wp1261 : Base 4 → WsL → ⟪ (ℓ "丨五") ⟫ʷ ≈ ⟪ (ℓ "丨亪五亪") ⟫ʷ
wp1261 c4 L = pw3 c4 L (ℓ "丨五") (ℓ "丨亪五亪") tt tt Eq.refl

wp1262 : Base 4 → WsL → ⟪ (ℓ "丨") ⟫ʷ ≈ ⟪ (ℓ "亮丶丨五亮丷亮丶亮丷") ⟫ʷ
wp1262 c4 L = pw2 c4 L (ℓ "丨") (ℓ "亮丶丨五亮丷亮丶亮丷") tt tt Eq.refl

wp1263 : Base 4 → WsL → ⟪ (ℓ "丌") ⟫ʷ ≈ ⟪ (ℓ "並亁並亁") ⟫ʷ
wp1263 c4 L = pw1 c4 L (ℓ "丌") (ℓ "並亁並亁") tt tt Eq.refl

wp1264 : Base 4 → WsL → ⟪ (ℓ "亁五丨丨丨丨丨丨丨丌丨丌丨丐丐丐一丐丽丽丽丽丽丽丽丽丽丨丌丨丌丨丐丐丐一丨丨丽丽丽亁丽") ⟫ʷ ≈ ⟪ (ℓ "丽亁亁五丨丨丨丨丨丨丨丌丨丌丨丐丐丐一丐丽丽丽丽丽丽丽丽丽丨丌丨丌丨丐丐丐一丨丨丽丽丽") ⟫ʷ
wp1264 c4 L = pw2 c4 L (ℓ "亁五丨丨丨丨丨丨丨丌丨丌丨丐丐丐一丐丽丽丽丽丽丽丽丽丽丨丌丨丌丨丐丐丐一丨丨丽丽丽亁丽") (ℓ "丽亁亁五丨丨丨丨丨丨丨丌丨丌丨丐丐丐一丐丽丽丽丽丽丽丽丽丽丨丌丨丌丨丐丐丐一丨丨丽丽丽") tt tt Eq.refl

wp1265 : Base 4 → WsL → ⟪ (ℓ "乇亨") ⟫ʷ ≈ ⟪ (ℓ "乇亝亨亝") ⟫ʷ
wp1265 c4 L = pw3 c4 L (ℓ "乇亨") (ℓ "乇亝亨亝") tt tt Eq.refl

wp1266 : Base 4 → WsL → ⟪ (ℓ "亄亨乇乇乇乇乇乇乇丒乇丒乇世世世丂世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世丂乇乇乕乕乕亄乕") ⟫ʷ ≈ ⟪ (ℓ "乕亄亄亨乇乇乇乇乇乇乇丒乇丒乇世世世丂世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世丂乇乇乕乕乕") ⟫ʷ
wp1266 c4 L = pw0 c4 L (ℓ "亄亨乇乇乇乇乇乇乇丒乇丒乇世世世丂世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世丂乇乇乕乕乕亄乕") (ℓ "乕亄亄亨乇乇乇乇乇乇乇丒乇丒乇世世世丂世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世丂乇乇乕乕乕") tt tt Eq.refl

wp1267 : Base 4 → WsL → ⟪ (ℓ "上") ⟫ʷ ≈ ⟪ (ℓ "並丽並丽") ⟫ʷ
wp1267 c4 L = pw1 c4 L (ℓ "上") (ℓ "並丽並丽") tt tt Eq.refl

wp1268 : Base 4 → WsL → ⟪ (ℓ "亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕亄乕") ⟫ʷ ≈ ⟪ (ℓ "乕亄亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕") ⟫ʷ
wp1268 c4 L = pw2 c4 L (ℓ "亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕亄乕") (ℓ "乕亄亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕") tt tt Eq.refl

wp1269 : Base 4 → WsL → ⟪ (ℓ "亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乇乇乩乩乩亇乩") ⟫ʷ ≈ ⟪ (ℓ "乩亇亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乇乇乩乩乩") ⟫ʷ
wp1269 c4 L = pw0 c4 L (ℓ "亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乇乇乩乩乩亇乩") (ℓ "乩亇亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乇乇乩乩乩") tt tt Eq.refl

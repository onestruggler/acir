------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP07 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wp1270 : Base 4 → WsL → ⟪ (ℓ "亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕亄亄亨乇乇乇乇乇乇乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乇乇乕乕乕") ⟫ʷ ≈ ⟪ (ℓ "亄亨乇乇乇乇乇乇乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乇乇乕乕乕亄亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕") ⟫ʷ
wp1270 c4 L = pw3 c4 L (ℓ "亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕亄亄亨乇乇乇乇乇乇乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乇乇乕乕乕") (ℓ "亄亨乇乇乇乇乇乇乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乇乇乕乕乕亄亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕") tt tt Eq.refl

wp1271 : Base 4 → WsL → ⟪ (ℓ "亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乇乇乩乩乩亇亇亰乢乢乢乢乢乢乢丘乢丘乢东东东丂东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东丂乢乢乩乩乩") ⟫ʷ ≈ ⟪ (ℓ "亇亰乢乢乢乢乢乢乢丘乢丘乢东东东丂东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东丂乢乢乩乩乩亇亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乇乇乩乩乩") ⟫ʷ
wp1271 c4 L = pw0 c4 L (ℓ "亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乇乇乩乩乩亇亇亰乢乢乢乢乢乢乢丘乢丘乢东东东丂东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东丂乢乢乩乩乩") (ℓ "亇亰乢乢乢乢乢乢乢丘乢丘乢东东东丂东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东丂乢乢乩乩乩亇亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乇乇乩乩乩") tt tt Eq.refl

wp1272 : Base 4 → WsL → ⟪ (ℓ "亄丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一乕乕乕亄亄乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乕乕乕") ⟫ʷ ≈ ⟪ (ℓ "亄乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乕乕乕亄亄丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一乕乕乕") ⟫ʷ
wp1272 c4 L = pw3 c4 L (ℓ "亄丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一乕乕乕亄亄乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乕乕乕") (ℓ "亄乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乕乕乕亄亄丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一乕乕乕") tt tt Eq.refl

wp1273 : Base 4 → WsL → ⟪ (ℓ "亇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乩乩乩亇亇乢丘乢丘乢东东东丂东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东丂乩乩乩") ⟫ʷ ≈ ⟪ (ℓ "亇乢丘乢丘乢东东东丂东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东丂乩乩乩亇亇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乩乩乩") ⟫ʷ
wp1273 c4 L = pw0 c4 L (ℓ "亇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乩乩乩亇亇乢丘乢丘乢东东东丂东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东丂乩乩乩") (ℓ "亇乢丘乢丘乢东东东丂东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东丂乩乩乩亇亇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乩乩乩") tt tt Eq.refl

wp1274 : Base 4 → WsL → ⟪ (ℓ "並亁並並丽並並丽並並亁並並丢並並亁並並丽並並丽並並亁並並丢並") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp1274 c4 L = pw1 c4 L (ℓ "並亁並並丽並並丽並並亁並並丢並並亁並並丽並並丽並並亁並並丢並") [] tt tt Eq.refl

wp1275 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "亏五亏") ⟫ʷ
wp1275 c4 L = pw3 c4 L (ℓ "五") (ℓ "亏五亏") tt tt Eq.refl

wp1276 : Base 4 → WsL → ⟪ (ℓ "五亓乹") ⟫ʷ ≈ ⟪ (ℓ "亓乹五") ⟫ʷ
wp1276 c4 L = pw2 c4 L (ℓ "五亓乹") (ℓ "亓乹五") tt tt Eq.refl

wp1277 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "亓乹亓乺亓乹亓乺") ⟫ʷ
wp1277 c4 L = pw2 c4 L (ℓ "五") (ℓ "亓乹亓乺亓乹亓乺") tt tt Eq.refl

wp1278 : Base 4 → WsL → ⟪ (ℓ "亜与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与亜") ⟫ʷ
wp1278 c4 L = pw1 c4 L (ℓ "亜与上与") (ℓ "与上与亜") tt tt Eq.refl

wp1279 : Base 4 → WsL → ⟪ (ℓ "亓乹亓乺与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与亓乹亓乺") ⟫ʷ
wp1279 c4 L = pw2 c4 L (ℓ "亓乹亓乺与上与") (ℓ "与上与亓乹亓乺") tt tt Eq.refl

wp1280 : Base 4 → WsL → ⟪ (ℓ "亜与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与亜") ⟫ʷ
wp1280 c4 L = pw1 c4 L (ℓ "亜与丽与") (ℓ "与丽与亜") tt tt Eq.refl

wp1281 : Base 4 → WsL → ⟪ (ℓ "丢举") ⟫ʷ ≈ ⟪ (ℓ "与丽与") ⟫ʷ
wp1281 c4 L = pw1 c4 L (ℓ "丢举") (ℓ "与丽与") tt tt Eq.refl

wp1282 : Base 4 → WsL → ⟪ (ℓ "亜丢举") ⟫ʷ ≈ ⟪ (ℓ "丢举亜") ⟫ʷ
wp1282 c4 L = pw1 c4 L (ℓ "亜丢举") (ℓ "丢举亜") tt tt Eq.refl

wp1283 : Base 4 → WsL → ⟪ (ℓ "丢举亓乹亓乺") ⟫ʷ ≈ ⟪ (ℓ "亓乹亓乺丢举") ⟫ʷ
wp1283 c4 L = pw2 c4 L (ℓ "丢举亓乹亓乺") (ℓ "亓乹亓乺丢举") tt tt Eq.refl

wp1284 : Base 4 → WsL → ⟪ (ℓ "亜与乫") ⟫ʷ ≈ ⟪ (ℓ "与亜") ⟫ʷ
wp1284 c4 L = pw1 c4 L (ℓ "亜与乫") (ℓ "与亜") tt tt Eq.refl

wp1285 : Base 4 → WsL → ⟪ (ℓ "亜乫") ⟫ʷ ≈ ⟪ (ℓ "乫亜") ⟫ʷ
wp1285 c4 L = pw1 c4 L (ℓ "亜乫") (ℓ "乫亜") tt tt Eq.refl

wp1286 : Base 4 → WsL → ⟪ (ℓ "五亓乹五亓乺与京") ⟫ʷ ≈ ⟪ (ℓ "京五亓乹五亓乺与") ⟫ʷ
wp1286 c4 L = pw2 c4 L (ℓ "五亓乹五亓乺与京") (ℓ "京五亓乹五亓乺与") tt tt Eq.refl

wp1287 : Base 4 → WsL → ⟪ (ℓ "乒亓亓乹亓乺") ⟫ʷ ≈ ⟪ (ℓ "亓乹亓乺乒亓") ⟫ʷ
wp1287 c4 L = pw2 c4 L (ℓ "乒亓亓乹亓乺") (ℓ "亓乹亓乺乒亓") tt tt Eq.refl

wp1288 : Base 4 → WsL → ⟪ (ℓ "亜亏") ⟫ʷ ≈ ⟪ (ℓ "亏五亜") ⟫ʷ
wp1288 c4 L = pw3 c4 L (ℓ "亜亏") (ℓ "亏五亜") tt tt Eq.refl

wp1289 : Base 4 → WsL → ⟪ (ℓ "五乒五亓") ⟫ʷ ≈ ⟪ (ℓ "乒亓") ⟫ʷ
wp1289 c4 L = pw2 c4 L (ℓ "五乒五亓") (ℓ "乒亓") tt tt Eq.refl

wp1290 : Base 4 → WsL → ⟪ (ℓ "乹亓乹亓乺") ⟫ʷ ≈ ⟪ (ℓ "亓乹亓乺乹") ⟫ʷ
wp1290 c4 L = pw2 c4 L (ℓ "乹亓乹亓乺") (ℓ "亓乹亓乺乹") tt tt Eq.refl

wp1291 : Base 4 → WsL → ⟪ (ℓ "乺亓乹亓乺") ⟫ʷ ≈ ⟪ (ℓ "亓乹亓乺乺") ⟫ʷ
wp1291 c4 L = pw2 c4 L (ℓ "乺亓乹亓乺") (ℓ "亓乹亓乺乺") tt tt Eq.refl

wp1292 : Base 4 → WsL → ⟪ (ℓ "亓乹亓乺与中与") ⟫ʷ ≈ ⟪ (ℓ "与中与亓乹亓乺") ⟫ʷ
wp1292 c4 L = pw2 c4 L (ℓ "亓乹亓乺与中与") (ℓ "与中与亓乹亓乺") tt tt Eq.refl

wp1293 : Base 4 → WsL → ⟪ (ℓ "中与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与中") ⟫ʷ
wp1293 c4 L = pw2 c4 L (ℓ "中与丽与") (ℓ "与丽与中") tt tt Eq.refl

wp1294 : Base 4 → WsL → ⟪ (ℓ "丒中上亓乹亓乺") ⟫ʷ ≈ ⟪ (ℓ "亓乹亓乺丒中上") ⟫ʷ
wp1294 c4 L = pw2 c4 L (ℓ "丒中上亓乹亓乺") (ℓ "亓乹亓乺丒中上") tt tt Eq.refl

wp1295 : Base 4 → WsL → ⟪ (ℓ "丽与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与丽") ⟫ʷ
wp1295 c4 L = pw1 c4 L (ℓ "丽与上与") (ℓ "与上与丽") tt tt Eq.refl

wp1296 : Base 4 → WsL → ⟪ (ℓ "丽与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与丽") ⟫ʷ
wp1296 c4 L = pw1 c4 L (ℓ "丽与丽与") (ℓ "与丽与丽") tt tt Eq.refl

wp1297 : Base 4 → WsL → ⟪ (ℓ "丢举与") ⟫ʷ ≈ ⟪ (ℓ "与丽") ⟫ʷ
wp1297 c4 L = pw1 c4 L (ℓ "丢举与") (ℓ "与丽") tt tt Eq.refl

wp1298 : Base 4 → WsL → ⟪ (ℓ "丽与") ⟫ʷ ≈ ⟪ (ℓ "与丢举") ⟫ʷ
wp1298 c4 L = pw1 c4 L (ℓ "丽与") (ℓ "与丢举") tt tt Eq.refl

wp1299 : Base 4 → WsL → ⟪ (ℓ "丽与中与") ⟫ʷ ≈ ⟪ (ℓ "与中与丽") ⟫ʷ
wp1299 c4 L = pw2 c4 L (ℓ "丽与中与") (ℓ "与中与丽") tt tt Eq.refl

wp1300 : Base 4 → WsL → ⟪ (ℓ "上与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与上") ⟫ʷ
wp1300 c4 L = pw1 c4 L (ℓ "上与丽与") (ℓ "与丽与上") tt tt Eq.refl

wp1301 : Base 4 → WsL → ⟪ (ℓ "亓乹亓乺一下") ⟫ʷ ≈ ⟪ (ℓ "一下亓乹亓乺") ⟫ʷ
wp1301 c4 L = pw2 c4 L (ℓ "亓乹亓乺一下") (ℓ "一下亓乹亓乺") tt tt Eq.refl

wp1302 : Base 4 → WsL → ⟪ (ℓ "亜一下") ⟫ʷ ≈ ⟪ (ℓ "一下亜") ⟫ʷ
wp1302 c4 L = pw1 c4 L (ℓ "亜一下") (ℓ "一下亜") tt tt Eq.refl

wp1303 : Base 4 → WsL → ⟪ (ℓ "丨与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与丨") ⟫ʷ
wp1303 c4 L = pw2 c4 L (ℓ "丨与丽与") (ℓ "与丽与丨") tt tt Eq.refl

wp1304 : Base 4 → WsL → ⟪ (ℓ "丐丩亓乹亓乺") ⟫ʷ ≈ ⟪ (ℓ "亓乹亓乺丐丩") ⟫ʷ
wp1304 c4 L = pw2 c4 L (ℓ "丐丩亓乹亓乺") (ℓ "亓乹亓乺丐丩") tt tt Eq.refl

wp1305 : Base 4 → WsL → ⟪ (ℓ "亜丐丩") ⟫ʷ ≈ ⟪ (ℓ "丐丩亜") ⟫ʷ
wp1305 c4 L = pw3 c4 L (ℓ "亜丐丩") (ℓ "丐丩亜") tt tt Eq.refl

wp1306 : Base 4 → WsL → ⟪ (ℓ "丢") ⟫ʷ ≈ ⟪ (ℓ "与丽与丽") ⟫ʷ
wp1306 c4 L = pw1 c4 L (ℓ "丢") (ℓ "与丽与丽") tt tt Eq.refl

wp1307 : Base 4 → WsL → ⟪ (ℓ "亓乹亓乺") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷") ⟫ʷ
wp1307 c4 L = pw2 c4 L (ℓ "亓乹亓乺") (ℓ "亮丶亮丷") tt tt Eq.refl

wp1308 : Base 4 → WsL → ⟪ (ℓ "亄乕五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕") ⟫ʷ ≈ ⟪ (ℓ "与五乕丒乕丒乕丢丢丢一丢乕乕乕乕丒乕丒乕丢丢丢一丢丨丨丨乕丒乕丒乕丢丢丢一乕乕丒乕丒乕丢丢丢一丨与") ⟫ʷ
wp1308 c4 L = pw2 c4 L (ℓ "亄乕五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕") (ℓ "与五乕丒乕丒乕丢丢丢一丢乕乕乕乕丒乕丒乕丢丢丢一丢丨丨丨乕丒乕丒乕丢丢丢一乕乕丒乕丒乕丢丢丢一丨与") tt tt Eq.refl

wp1309 : Base 4 → WsL → ⟪ (ℓ "亜亟") ⟫ʷ ≈ ⟪ (ℓ "亟亜丱") ⟫ʷ
wp1309 c4 L = pw3 c4 L (ℓ "亜亟") (ℓ "亟亜丱") tt tt Eq.refl

wp1310 : Base 4 → WsL → ⟪ (ℓ "亜丱亟亜") ⟫ʷ ≈ ⟪ (ℓ "亟") ⟫ʷ
wp1310 c4 L = pw3 c4 L (ℓ "亜丱亟亜") (ℓ "亟") tt tt Eq.refl

wp1311 : Base 4 → WsL → ⟪ (ℓ "为亟") ⟫ʷ ≈ ⟪ (ℓ "亟为") ⟫ʷ
wp1311 c4 L = pw1 c4 L (ℓ "为亟") (ℓ "亟为") tt tt Eq.refl

wp1312 : Base 4 → WsL → ⟪ (ℓ "京为五") ⟫ʷ ≈ ⟪ (ℓ "为京") ⟫ʷ
wp1312 c4 L = pw2 c4 L (ℓ "京为五") (ℓ "为京") tt tt Eq.refl

wp1313 : Base 4 → WsL → ⟪ (ℓ "五亟") ⟫ʷ ≈ ⟪ (ℓ "亟五二") ⟫ʷ
wp1313 c4 L = pw3 c4 L (ℓ "五亟") (ℓ "亟五二") tt tt Eq.refl

wp1314 : Base 4 → WsL → ⟪ (ℓ "为五五") ⟫ʷ ≈ ⟪ (ℓ "为") ⟫ʷ
wp1314 c4 L = pw2 c4 L (ℓ "为五五") (ℓ "为") tt tt Eq.refl

wp1315 : Base 4 → WsL → ⟪ (ℓ "买亟") ⟫ʷ ≈ ⟪ (ℓ "亟买亳") ⟫ʷ
wp1315 c4 L = pw1 c4 L (ℓ "买亟") (ℓ "亟买亳") tt tt Eq.refl

wp1316 : Base 4 → WsL → ⟪ (ℓ "乇亟") ⟫ʷ ≈ ⟪ (ℓ "亟乇") ⟫ʷ
wp1316 c4 L = pw3 c4 L (ℓ "乇亟") (ℓ "亟乇") tt tt Eq.refl

wp1317 : Base 4 → WsL → ⟪ (ℓ "书亟") ⟫ʷ ≈ ⟪ (ℓ "亟书") ⟫ʷ
wp1317 c4 L = pw1 c4 L (ℓ "书亟") (ℓ "亟书") tt tt Eq.refl

wp1318 : Base 4 → WsL → ⟪ (ℓ "亟亳") ⟫ʷ ≈ ⟪ (ℓ "亳亟") ⟫ʷ
wp1318 c4 L = pw1 c4 L (ℓ "亟亳") (ℓ "亳亟") tt tt Eq.refl

wp1319 : Base 4 → WsL → ⟪ (ℓ "买亳亳") ⟫ʷ ≈ ⟪ (ℓ "买") ⟫ʷ
wp1319 c4 L = pw1 c4 L (ℓ "买亳亳") (ℓ "买") tt tt Eq.refl

wp1320 : Base 4 → WsL → ⟪ (ℓ "丒中上亗") ⟫ʷ ≈ ⟪ (ℓ "亗丒中上") ⟫ʷ
wp1320 c4 L = pw2 c4 L (ℓ "丒中上亗") (ℓ "亗丒中上") tt tt Eq.refl

wp1321 : Base 4 → WsL → ⟪ (ℓ "两亜严") ⟫ʷ ≈ ⟪ (ℓ "亟") ⟫ʷ
wp1321 c4 L = pw1 c4 L (ℓ "两亜严") (ℓ "亟") tt tt Eq.refl

wp1322 : Base 4 → WsL → ⟪ (ℓ "丰丢亟丣") ⟫ʷ ≈ ⟪ (ℓ "亟亜") ⟫ʷ
wp1322 c4 L = pw3 c4 L (ℓ "丰丢亟丣") (ℓ "亟亜") tt tt Eq.refl

wp1323 : Base 4 → WsL → ⟪ (ℓ "亟亟") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp1323 c4 L = pw1 c4 L (ℓ "亟亟") [] tt tt Eq.refl

wp1324 : Base 4 → WsL → ⟪ (ℓ "亜与临与") ⟫ʷ ≈ ⟪ (ℓ "与临与亜") ⟫ʷ
wp1324 c4 L = pw3 c4 L (ℓ "亜与临与") (ℓ "与临与亜") tt tt Eq.refl

wp1325 : Base 4 → WsL → ⟪ (ℓ "京亗") ⟫ʷ ≈ ⟪ (ℓ "亗京亐") ⟫ʷ
wp1325 c4 L = pw2 c4 L (ℓ "京亗") (ℓ "亗京亐") tt tt Eq.refl

wp1326 : Base 4 → WsL → ⟪ (ℓ "也亗") ⟫ʷ ≈ ⟪ (ℓ "亗也亟") ⟫ʷ
wp1326 c4 L = pw3 c4 L (ℓ "也亗") (ℓ "亗也亟") tt tt Eq.refl

wp1327 : Base 4 → WsL → ⟪ (ℓ "亰亟亘") ⟫ʷ ≈ ⟪ (ℓ "亟亰") ⟫ʷ
wp1327 c4 L = pw1 c4 L (ℓ "亰亟亘") (ℓ "亟亰") tt tt Eq.refl

wp1328 : Base 4 → WsL → ⟪ (ℓ "丶亗") ⟫ʷ ≈ ⟪ (ℓ "亗丶") ⟫ʷ
wp1328 c4 L = pw2 c4 L (ℓ "丶亗") (ℓ "亗丶") tt tt Eq.refl

wp1329 : Base 4 → WsL → ⟪ (ℓ "亗亟") ⟫ʷ ≈ ⟪ (ℓ "亟亗") ⟫ʷ
wp1329 c4 L = pw3 c4 L (ℓ "亗亟") (ℓ "亟亗") tt tt Eq.refl

wp1330 : Base 4 → WsL → ⟪ (ℓ "也亟亟") ⟫ʷ ≈ ⟪ (ℓ "也") ⟫ʷ
wp1330 c4 L = pw3 c4 L (ℓ "也亟亟") (ℓ "也") tt tt Eq.refl

wp1331 : Base 4 → WsL → ⟪ (ℓ "五井丸井五丸") ⟫ʷ ≈ ⟪ (ℓ "京") ⟫ʷ
wp1331 c4 L = pw2 c4 L (ℓ "五井丸井五丸") (ℓ "京") tt tt Eq.refl

wp1332 : Base 4 → WsL → ⟪ (ℓ "丘临上亟") ⟫ʷ ≈ ⟪ (ℓ "亟丘临上") ⟫ʷ
wp1332 c4 L = pw3 c4 L (ℓ "丘临上亟") (ℓ "亟丘临上") tt tt Eq.refl

wp1333 : Base 4 → WsL → ⟪ (ℓ "买亳") ⟫ʷ ≈ ⟪ (ℓ "亳买") ⟫ʷ
wp1333 c4 L = pw1 c4 L (ℓ "买亳") (ℓ "亳买") tt tt Eq.refl

wp1334 : Base 4 → WsL → ⟪ (ℓ "为亳") ⟫ʷ ≈ ⟪ (ℓ "亳为亟") ⟫ʷ
wp1334 c4 L = pw1 c4 L (ℓ "为亳") (ℓ "亳为亟") tt tt Eq.refl

wp1335 : Base 4 → WsL → ⟪ (ℓ "五亟二") ⟫ʷ ≈ ⟪ (ℓ "亟五") ⟫ʷ
wp1335 c4 L = pw3 c4 L (ℓ "五亟二") (ℓ "亟五") tt tt Eq.refl

wp1336 : Base 4 → WsL → ⟪ (ℓ "乜亳") ⟫ʷ ≈ ⟪ (ℓ "亳乜") ⟫ʷ
wp1336 c4 L = pw1 c4 L (ℓ "乜亳") (ℓ "亳乜") tt tt Eq.refl

wp1337 : Base 4 → WsL → ⟪ (ℓ "为亟亟") ⟫ʷ ≈ ⟪ (ℓ "为") ⟫ʷ
wp1337 c4 L = pw1 c4 L (ℓ "为亟亟") (ℓ "为") tt tt Eq.refl

wp1338 : Base 4 → WsL → ⟪ (ℓ "五个亗") ⟫ʷ ≈ ⟪ (ℓ "亗五") ⟫ʷ
wp1338 c4 L = pw2 c4 L (ℓ "五个亗") (ℓ "亗五") tt tt Eq.refl

wp1339 : Base 4 → WsL → ⟪ (ℓ "五个") ⟫ʷ ≈ ⟪ (ℓ "亗五亗") ⟫ʷ
wp1339 c4 L = pw2 c4 L (ℓ "五个") (ℓ "亗五亗") tt tt Eq.refl

wp1340 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "个五个") ⟫ʷ
wp1340 c4 L = pw2 c4 L (ℓ "五") (ℓ "个五个") tt tt Eq.refl

wp1341 : Base 4 → WsL → ⟪ (ℓ "亜亗") ⟫ʷ ≈ ⟪ (ℓ "亗亜二") ⟫ʷ
wp1341 c4 L = pw3 c4 L (ℓ "亜亗") (ℓ "亗亜二") tt tt Eq.refl

wp1342 : Base 4 → WsL → ⟪ (ℓ "丟亗") ⟫ʷ ≈ ⟪ (ℓ "亗丟") ⟫ʷ
wp1342 c4 L = pw2 c4 L (ℓ "丟亗") (ℓ "亗丟") tt tt Eq.refl

wp1343 : Base 4 → WsL → ⟪ (ℓ "丯亗") ⟫ʷ ≈ ⟪ (ℓ "亗丯") ⟫ʷ
wp1343 c4 L = pw3 c4 L (ℓ "丯亗") (ℓ "亗丯") tt tt Eq.refl

wp1344 : Base 4 → WsL → ⟪ (ℓ "丷亗") ⟫ʷ ≈ ⟪ (ℓ "亗丷") ⟫ʷ
wp1344 c4 L = pw2 c4 L (ℓ "丷亗") (ℓ "亗丷") tt tt Eq.refl

wp1345 : Base 4 → WsL → ⟪ (ℓ "丞亗") ⟫ʷ ≈ ⟪ (ℓ "亗丞") ⟫ʷ
wp1345 c4 L = pw2 c4 L (ℓ "丞亗") (ℓ "亗丞") tt tt Eq.refl

wp1346 : Base 4 → WsL → ⟪ (ℓ "些亜亜") ⟫ʷ ≈ ⟪ (ℓ "些") ⟫ʷ
wp1346 c4 L = pw1 c4 L (ℓ "些亜亜") (ℓ "些") tt tt Eq.refl

wp1347 : Base 4 → WsL → ⟪ (ℓ "丶亳") ⟫ʷ ≈ ⟪ (ℓ "亳丶") ⟫ʷ
wp1347 c4 L = pw1 c4 L (ℓ "丶亳") (ℓ "亳丶") tt tt Eq.refl

wp1348 : Base 4 → WsL → ⟪ (ℓ "丷亳") ⟫ʷ ≈ ⟪ (ℓ "亳丷") ⟫ʷ
wp1348 c4 L = pw1 c4 L (ℓ "丷亳") (ℓ "亳丷") tt tt Eq.refl

wp1349 : Base 4 → WsL → ⟪ (ℓ "五乳互") ⟫ʷ ≈ ⟪ (ℓ "乳互五") ⟫ʷ
wp1349 c4 L = pw2 c4 L (ℓ "五乳互") (ℓ "乳互五") tt tt Eq.refl

wp1350 : Base 4 → WsL → ⟪ (ℓ "五丒中上") ⟫ʷ ≈ ⟪ (ℓ "丒中上五") ⟫ʷ
wp1350 c4 L = pw2 c4 L (ℓ "五丒中上") (ℓ "丒中上五") tt tt Eq.refl

wp1351 : Base 4 → WsL → ⟪ (ℓ "五与乗") ⟫ʷ ≈ ⟪ (ℓ "与五") ⟫ʷ
wp1351 c4 L = pw2 c4 L (ℓ "五与乗") (ℓ "与五") tt tt Eq.refl

wp1352 : Base 4 → WsL → ⟪ (ℓ "五乗") ⟫ʷ ≈ ⟪ (ℓ "乗五") ⟫ʷ
wp1352 c4 L = pw2 c4 L (ℓ "五乗") (ℓ "乗五") tt tt Eq.refl

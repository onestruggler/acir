------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP08 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wp1353 : Base 4 → WsL → ⟪ (ℓ "与乗乗") ⟫ʷ ≈ ⟪ (ℓ "与") ⟫ʷ
wp1353 c4 L = pw2 c4 L (ℓ "与乗乗") (ℓ "与") tt tt Eq.refl

wp1354 : Base 4 → WsL → ⟪ (ℓ "些亳") ⟫ʷ ≈ ⟪ (ℓ "亳亟些") ⟫ʷ
wp1354 c4 L = pw1 c4 L (ℓ "些亳") (ℓ "亳亟些") tt tt Eq.refl

wp1355 : Base 4 → WsL → ⟪ (ℓ "丰亳") ⟫ʷ ≈ ⟪ (ℓ "亳丰") ⟫ʷ
wp1355 c4 L = pw1 c4 L (ℓ "丰亳") (ℓ "亳丰") tt tt Eq.refl

wp1356 : Base 4 → WsL → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "亟二亟") ⟫ʷ
wp1356 c4 L = pw3 c4 L (ℓ "二") (ℓ "亟二亟") tt tt Eq.refl

wp1357 : Base 4 → WsL → ⟪ (ℓ "亟些亳") ⟫ʷ ≈ ⟪ (ℓ "亳些") ⟫ʷ
wp1357 c4 L = pw1 c4 L (ℓ "亟些亳") (ℓ "亳些") tt tt Eq.refl

wp1358 : Base 4 → WsL → ⟪ (ℓ "五亟") ⟫ʷ ≈ ⟪ (ℓ "亟二五") ⟫ʷ
wp1358 c4 L = pw3 c4 L (ℓ "五亟") (ℓ "亟二五") tt tt Eq.refl

wp1359 : Base 4 → WsL → ⟪ (ℓ "亟与临与") ⟫ʷ ≈ ⟪ (ℓ "与临与亟") ⟫ʷ
wp1359 c4 L = pw3 c4 L (ℓ "亟与临与") (ℓ "与临与亟") tt tt Eq.refl

wp1360 : Base 4 → WsL → ⟪ (ℓ "五与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与五") ⟫ʷ
wp1360 c4 L = pw2 c4 L (ℓ "五与上与") (ℓ "与上与五") tt tt Eq.refl

wp1361 : Base 4 → WsL → ⟪ (ℓ "亯与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与亯") ⟫ʷ
wp1361 c4 L = pw2 c4 L (ℓ "亯与上与") (ℓ "与上与亯") tt tt Eq.refl

wp1362 : Base 4 → WsL → ⟪ (ℓ "亯一下") ⟫ʷ ≈ ⟪ (ℓ "一下亯") ⟫ʷ
wp1362 c4 L = pw2 c4 L (ℓ "亯一下") (ℓ "一下亯") tt tt Eq.refl

wp1363 : Base 4 → WsL → ⟪ (ℓ "亜丘临上") ⟫ʷ ≈ ⟪ (ℓ "丘临上亜") ⟫ʷ
wp1363 c4 L = pw3 c4 L (ℓ "亜丘临上") (ℓ "丘临上亜") tt tt Eq.refl

wp1364 : Base 4 → WsL → ⟪ (ℓ "五互亠") ⟫ʷ ≈ ⟪ (ℓ "互五") ⟫ʷ
wp1364 c4 L = pw2 c4 L (ℓ "五互亠") (ℓ "互五") tt tt Eq.refl

wp1365 : Base 4 → WsL → ⟪ (ℓ "亠亳") ⟫ʷ ≈ ⟪ (ℓ "亳亠亘") ⟫ʷ
wp1365 c4 L = pw1 c4 L (ℓ "亠亳") (ℓ "亳亠亘") tt tt Eq.refl

wp1366 : Base 4 → WsL → ⟪ (ℓ "互亠亠") ⟫ʷ ≈ ⟪ (ℓ "互") ⟫ʷ
wp1366 c4 L = pw2 c4 L (ℓ "互亠亠") (ℓ "互") tt tt Eq.refl

wp1367 : Base 4 → WsL → ⟪ (ℓ "亘亳") ⟫ʷ ≈ ⟪ (ℓ "亳亘") ⟫ʷ
wp1367 c4 L = pw1 c4 L (ℓ "亘亳") (ℓ "亳亘") tt tt Eq.refl

wp1368 : Base 4 → WsL → ⟪ (ℓ "亰书些") ⟫ʷ ≈ ⟪ (ℓ "书些乫亜亰") ⟫ʷ
wp1368 c4 L = pw1 c4 L (ℓ "亰书些") (ℓ "书些乫亜亰") tt tt Eq.refl

wp1369 : Base 4 → WsL → ⟪ (ℓ "乫二亗") ⟫ʷ ≈ ⟪ (ℓ "亗乫") ⟫ʷ
wp1369 c4 L = pw3 c4 L (ℓ "乫二亗") (ℓ "亗乫") tt tt Eq.refl

wp1370 : Base 4 → WsL → ⟪ (ℓ "亜二亗") ⟫ʷ ≈ ⟪ (ℓ "亗亜") ⟫ʷ
wp1370 c4 L = pw3 c4 L (ℓ "亜二亗") (ℓ "亗亜") tt tt Eq.refl

wp1371 : Base 4 → WsL → ⟪ (ℓ "乫二亜二") ⟫ʷ ≈ ⟪ (ℓ "乫亜") ⟫ʷ
wp1371 c4 L = pw3 c4 L (ℓ "乫二亜二") (ℓ "乫亜") tt tt Eq.refl

wp1372 : Base 4 → WsL → ⟪ (ℓ "亰书些乫亜") ⟫ʷ ≈ ⟪ (ℓ "书些亰") ⟫ʷ
wp1372 c4 L = pw1 c4 L (ℓ "亰书些乫亜") (ℓ "书些亰") tt tt Eq.refl

wp1373 : Base 4 → WsL → ⟪ (ℓ "互亯") ⟫ʷ ≈ ⟪ (ℓ "亯亣互") ⟫ʷ
wp1373 c4 L = pw2 c4 L (ℓ "互亯") (ℓ "亯亣互") tt tt Eq.refl

wp1374 : Base 4 → WsL → ⟪ (ℓ "亜亣亘") ⟫ʷ ≈ ⟪ (ℓ "亣亜") ⟫ʷ
wp1374 c4 L = pw1 c4 L (ℓ "亜亣亘") (ℓ "亣亜") tt tt Eq.refl

wp1375 : Base 4 → WsL → ⟪ (ℓ "丷亯") ⟫ʷ ≈ ⟪ (ℓ "亯丷") ⟫ʷ
wp1375 c4 L = pw2 c4 L (ℓ "丷亯") (ℓ "亯丷") tt tt Eq.refl

wp1376 : Base 4 → WsL → ⟪ (ℓ "丶亯") ⟫ʷ ≈ ⟪ (ℓ "亯丶") ⟫ʷ
wp1376 c4 L = pw2 c4 L (ℓ "丶亯") (ℓ "亯丶") tt tt Eq.refl

wp1377 : Base 4 → WsL → ⟪ (ℓ "亣亯") ⟫ʷ ≈ ⟪ (ℓ "亯亣") ⟫ʷ
wp1377 c4 L = pw2 c4 L (ℓ "亣亯") (ℓ "亯亣") tt tt Eq.refl

wp1378 : Base 4 → WsL → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "亣亘亣") ⟫ʷ
wp1378 c4 L = pw1 c4 L (ℓ "亘") (ℓ "亣亘亣") tt tt Eq.refl

wp1379 : Base 4 → WsL → ⟪ (ℓ "亣互亯") ⟫ʷ ≈ ⟪ (ℓ "亯互") ⟫ʷ
wp1379 c4 L = pw2 c4 L (ℓ "亣互亯") (ℓ "亯互") tt tt Eq.refl

wp1380 : Base 4 → WsL → ⟪ (ℓ "亜乽") ⟫ʷ ≈ ⟪ (ℓ "乽亘亜") ⟫ʷ
wp1380 c4 L = pw1 c4 L (ℓ "亜乽") (ℓ "乽亘亜") tt tt Eq.refl

wp1381 : Base 4 → WsL → ⟪ (ℓ "亜亣") ⟫ʷ ≈ ⟪ (ℓ "亣亘亜") ⟫ʷ
wp1381 c4 L = pw1 c4 L (ℓ "亜亣") (ℓ "亣亘亜") tt tt Eq.refl

wp1382 : Base 4 → WsL → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "乽亘乽") ⟫ʷ
wp1382 c4 L = pw1 c4 L (ℓ "亘") (ℓ "乽亘乽") tt tt Eq.refl

wp1383 : Base 4 → WsL → ⟪ (ℓ "五一下") ⟫ʷ ≈ ⟪ (ℓ "一下五") ⟫ʷ
wp1383 c4 L = pw2 c4 L (ℓ "五一下") (ℓ "一下五") tt tt Eq.refl

wp1384 : Base 4 → WsL → ⟪ (ℓ "亣与主与") ⟫ʷ ≈ ⟪ (ℓ "与主与亣") ⟫ʷ
wp1384 c4 L = pw1 c4 L (ℓ "亣与主与") (ℓ "与主与亣") tt tt Eq.refl

wp1385 : Base 4 → WsL → ⟪ (ℓ "亨亟") ⟫ʷ ≈ ⟪ (ℓ "亟亨二") ⟫ʷ
wp1385 c4 L = pw3 c4 L (ℓ "亨亟") (ℓ "亟亨二") tt tt Eq.refl

wp1386 : Base 4 → WsL → ⟪ (ℓ "乶亟") ⟫ʷ ≈ ⟪ (ℓ "亟乶亣") ⟫ʷ
wp1386 c4 L = pw1 c4 L (ℓ "乶亟") (ℓ "亟乶亣") tt tt Eq.refl

wp1387 : Base 4 → WsL → ⟪ (ℓ "京亣亐") ⟫ʷ ≈ ⟪ (ℓ "亣京") ⟫ʷ
wp1387 c4 L = pw2 c4 L (ℓ "京亣亐") (ℓ "亣京") tt tt Eq.refl

wp1388 : Base 4 → WsL → ⟪ (ℓ "丨亟") ⟫ʷ ≈ ⟪ (ℓ "亟丨") ⟫ʷ
wp1388 c4 L = pw3 c4 L (ℓ "丨亟") (ℓ "亟丨") tt tt Eq.refl

wp1389 : Base 4 → WsL → ⟪ (ℓ "亟亣") ⟫ʷ ≈ ⟪ (ℓ "亣亟") ⟫ʷ
wp1389 c4 L = pw1 c4 L (ℓ "亟亣") (ℓ "亣亟") tt tt Eq.refl

wp1390 : Base 4 → WsL → ⟪ (ℓ "乶亣亣") ⟫ʷ ≈ ⟪ (ℓ "乶") ⟫ʷ
wp1390 c4 L = pw1 c4 L (ℓ "乶亣亣") (ℓ "乶") tt tt Eq.refl

wp1391 : Base 4 → WsL → ⟪ (ℓ "亠亣") ⟫ʷ ≈ ⟪ (ℓ "亣亠丸") ⟫ʷ
wp1391 c4 L = pw1 c4 L (ℓ "亠亣") (ℓ "亣亠丸") tt tt Eq.refl

wp1392 : Base 4 → WsL → ⟪ (ℓ "亠丸亣亠") ⟫ʷ ≈ ⟪ (ℓ "亣") ⟫ʷ
wp1392 c4 L = pw1 c4 L (ℓ "亠丸亣亠") (ℓ "亣") tt tt Eq.refl

wp1393 : Base 4 → WsL → ⟪ (ℓ "丞主上亣") ⟫ʷ ≈ ⟪ (ℓ "亣丞主上") ⟫ʷ
wp1393 c4 L = pw1 c4 L (ℓ "丞主上亣") (ℓ "亣丞主上") tt tt Eq.refl

wp1394 : Base 4 → WsL → ⟪ (ℓ "亗与中与") ⟫ʷ ≈ ⟪ (ℓ "与中与亗") ⟫ʷ
wp1394 c4 L = pw2 c4 L (ℓ "亗与中与") (ℓ "与中与亗") tt tt Eq.refl

wp1395 : Base 4 → WsL → ⟪ (ℓ "五与中与") ⟫ʷ ≈ ⟪ (ℓ "与中与五") ⟫ʷ
wp1395 c4 L = pw2 c4 L (ℓ "五与中与") (ℓ "与中与五") tt tt Eq.refl

wp1396 : Base 4 → WsL → ⟪ (ℓ "亠亯") ⟫ʷ ≈ ⟪ (ℓ "亯亠亐") ⟫ʷ
wp1396 c4 L = pw2 c4 L (ℓ "亠亯") (ℓ "亯亠亐") tt tt Eq.refl

wp1397 : Base 4 → WsL → ⟪ (ℓ "亜享二") ⟫ʷ ≈ ⟪ (ℓ "享亜") ⟫ʷ
wp1397 c4 L = pw3 c4 L (ℓ "亜享二") (ℓ "享亜") tt tt Eq.refl

wp1398 : Base 4 → WsL → ⟪ (ℓ "丨亯") ⟫ʷ ≈ ⟪ (ℓ "亯丨") ⟫ʷ
wp1398 c4 L = pw2 c4 L (ℓ "丨亯") (ℓ "亯丨") tt tt Eq.refl

wp1399 : Base 4 → WsL → ⟪ (ℓ "亠丸亣") ⟫ʷ ≈ ⟪ (ℓ "亣亠") ⟫ʷ
wp1399 c4 L = pw1 c4 L (ℓ "亠丸亣") (ℓ "亣亠") tt tt Eq.refl

wp1400 : Base 4 → WsL → ⟪ (ℓ "亠丸") ⟫ʷ ≈ ⟪ (ℓ "亣亠亣") ⟫ʷ
wp1400 c4 L = pw1 c4 L (ℓ "亠丸") (ℓ "亣亠亣") tt tt Eq.refl

wp1401 : Base 4 → WsL → ⟪ (ℓ "丬亣") ⟫ʷ ≈ ⟪ (ℓ "亣丬") ⟫ʷ
wp1401 c4 L = pw2 c4 L (ℓ "丬亣") (ℓ "亣丬") tt tt Eq.refl

wp1402 : Base 4 → WsL → ⟪ (ℓ "亜亣") ⟫ʷ ≈ ⟪ (ℓ "亣亜亘") ⟫ʷ
wp1402 c4 L = pw1 c4 L (ℓ "亜亣") (ℓ "亣亜亘") tt tt Eq.refl

wp1403 : Base 4 → WsL → ⟪ (ℓ "乄亣") ⟫ʷ ≈ ⟪ (ℓ "亣乄亯") ⟫ʷ
wp1403 c4 L = pw2 c4 L (ℓ "乄亣") (ℓ "亣乄亯") tt tt Eq.refl

wp1404 : Base 4 → WsL → ⟪ (ℓ "乢亣") ⟫ʷ ≈ ⟪ (ℓ "亣乢") ⟫ʷ
wp1404 c4 L = pw1 c4 L (ℓ "乢亣") (ℓ "亣乢") tt tt Eq.refl

wp1405 : Base 4 → WsL → ⟪ (ℓ "乳亣") ⟫ʷ ≈ ⟪ (ℓ "亣乳") ⟫ʷ
wp1405 c4 L = pw2 c4 L (ℓ "乳亣") (ℓ "亣乳") tt tt Eq.refl

wp1406 : Base 4 → WsL → ⟪ (ℓ "乄亯亯") ⟫ʷ ≈ ⟪ (ℓ "乄") ⟫ʷ
wp1406 c4 L = pw2 c4 L (ℓ "乄亯亯") (ℓ "乄") tt tt Eq.refl

wp1407 : Base 4 → WsL → ⟪ (ℓ "乄亯") ⟫ʷ ≈ ⟪ (ℓ "亯乄") ⟫ʷ
wp1407 c4 L = pw2 c4 L (ℓ "乄亯") (ℓ "亯乄") tt tt Eq.refl

wp1408 : Base 4 → WsL → ⟪ (ℓ "丬亯") ⟫ʷ ≈ ⟪ (ℓ "亯丬亣") ⟫ʷ
wp1408 c4 L = pw2 c4 L (ℓ "丬亯") (ℓ "亯丬亣") tt tt Eq.refl

wp1409 : Base 4 → WsL → ⟪ (ℓ "买亯") ⟫ʷ ≈ ⟪ (ℓ "亯买") ⟫ʷ
wp1409 c4 L = pw2 c4 L (ℓ "买亯") (ℓ "亯买") tt tt Eq.refl

wp1410 : Base 4 → WsL → ⟪ (ℓ "丬亣亣") ⟫ʷ ≈ ⟪ (ℓ "丬") ⟫ʷ
wp1410 c4 L = pw2 c4 L (ℓ "丬亣亣") (ℓ "丬") tt tt Eq.refl

wp1411 : Base 4 → WsL → ⟪ (ℓ "亜亠亚") ⟫ʷ ≈ ⟪ (ℓ "亚亜") ⟫ʷ
wp1411 c4 L = pw1 c4 L (ℓ "亜亠亚") (ℓ "亚亜") tt tt Eq.refl

wp1412 : Base 4 → WsL → ⟪ (ℓ "亐亯") ⟫ʷ ≈ ⟪ (ℓ "亯亐") ⟫ʷ
wp1412 c4 L = pw2 c4 L (ℓ "亐亯") (ℓ "亯亐") tt tt Eq.refl

wp1413 : Base 4 → WsL → ⟪ (ℓ "亜享") ⟫ʷ ≈ ⟪ (ℓ "享亜二") ⟫ʷ
wp1413 c4 L = pw3 c4 L (ℓ "亜享") (ℓ "享亜二") tt tt Eq.refl

wp1414 : Base 4 → WsL → ⟪ (ℓ "亠亯亐") ⟫ʷ ≈ ⟪ (ℓ "亯亠") ⟫ʷ
wp1414 c4 L = pw2 c4 L (ℓ "亠亯亐") (ℓ "亯亠") tt tt Eq.refl

wp1415 : Base 4 → WsL → ⟪ (ℓ "丨享") ⟫ʷ ≈ ⟪ (ℓ "享丨") ⟫ʷ
wp1415 c4 L = pw3 c4 L (ℓ "丨享") (ℓ "享丨") tt tt Eq.refl

wp1416 : Base 4 → WsL → ⟪ (ℓ "亜丱亟") ⟫ʷ ≈ ⟪ (ℓ "亟亜") ⟫ʷ
wp1416 c4 L = pw3 c4 L (ℓ "亜丱亟") (ℓ "亟亜") tt tt Eq.refl

wp1417 : Base 4 → WsL → ⟪ (ℓ "亜丱") ⟫ʷ ≈ ⟪ (ℓ "亟亜亟") ⟫ʷ
wp1417 c4 L = pw3 c4 L (ℓ "亜丱") (ℓ "亟亜亟") tt tt Eq.refl

wp1418 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "丱亜丱") ⟫ʷ
wp1418 c4 L = pw3 c4 L (ℓ "亜") (ℓ "丱亜丱") tt tt Eq.refl

wp1419 : Base 4 → WsL → ⟪ (ℓ "京互亠") ⟫ʷ ≈ ⟪ (ℓ "互亠京亠") ⟫ʷ
wp1419 c4 L = pw2 c4 L (ℓ "京互亠") (ℓ "互亠京亠") tt tt Eq.refl

wp1420 : Base 4 → WsL → ⟪ (ℓ "京亠互亠") ⟫ʷ ≈ ⟪ (ℓ "互亠京") ⟫ʷ
wp1420 c4 L = pw2 c4 L (ℓ "京亠互亠") (ℓ "互亠京") tt tt Eq.refl

wp1421 : Base 4 → WsL → ⟪ (ℓ "京与") ⟫ʷ ≈ ⟪ (ℓ "与京") ⟫ʷ
wp1421 c4 L = pw2 c4 L (ℓ "京与") (ℓ "与京") tt tt Eq.refl

wp1422 : Base 4 → WsL → ⟪ (ℓ "亠互") ⟫ʷ ≈ ⟪ (ℓ "互亠") ⟫ʷ
wp1422 c4 L = pw2 c4 L (ℓ "亠互") (ℓ "互亠") tt tt Eq.refl

wp1423 : Base 4 → WsL → ⟪ (ℓ "亗亓亯") ⟫ʷ ≈ ⟪ (ℓ "亯亓") ⟫ʷ
wp1423 c4 L = pw2 c4 L (ℓ "亗亓亯") (ℓ "亯亓") tt tt Eq.refl

wp1424 : Base 4 → WsL → ⟪ (ℓ "亜亗") ⟫ʷ ≈ ⟪ (ℓ "亗二亜") ⟫ʷ
wp1424 c4 L = pw3 c4 L (ℓ "亜亗") (ℓ "亗二亜") tt tt Eq.refl

wp1425 : Base 4 → WsL → ⟪ (ℓ "亗亯") ⟫ʷ ≈ ⟪ (ℓ "亯亗") ⟫ʷ
wp1425 c4 L = pw2 c4 L (ℓ "亗亯") (ℓ "亯亗") tt tt Eq.refl

wp1426 : Base 4 → WsL → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "亗二亗") ⟫ʷ
wp1426 c4 L = pw3 c4 L (ℓ "二") (ℓ "亗二亗") tt tt Eq.refl

wp1427 : Base 4 → WsL → ⟪ (ℓ "乹互") ⟫ʷ ≈ ⟪ (ℓ "互乹") ⟫ʷ
wp1427 c4 L = pw2 c4 L (ℓ "乹互") (ℓ "互乹") tt tt Eq.refl

wp1428 : Base 4 → WsL → ⟪ (ℓ "乺互") ⟫ʷ ≈ ⟪ (ℓ "互乺") ⟫ʷ
wp1428 c4 L = pw2 c4 L (ℓ "乺互") (ℓ "互乺") tt tt Eq.refl

wp1429 : Base 4 → WsL → ⟪ (ℓ "丯亞") ⟫ʷ ≈ ⟪ (ℓ "亞丯丽亜") ⟫ʷ
wp1429 c4 L = pw3 c4 L (ℓ "丯亞") (ℓ "亞丯丽亜") tt tt Eq.refl

wp1430 : Base 4 → WsL → ⟪ (ℓ "丯丽亜丽丿亜") ⟫ʷ ≈ ⟪ (ℓ "丯") ⟫ʷ
wp1430 c4 L = pw3 c4 L (ℓ "丯丽亜丽丿亜") (ℓ "丯") tt tt Eq.refl

wp1431 : Base 4 → WsL → ⟪ (ℓ "乹与临与") ⟫ʷ ≈ ⟪ (ℓ "与临与乹") ⟫ʷ
wp1431 c4 L = pw1 c4 L (ℓ "乹与临与") (ℓ "与临与乹") tt tt Eq.refl

wp1432 : Base 4 → WsL → ⟪ (ℓ "乺与临与") ⟫ʷ ≈ ⟪ (ℓ "与临与乺") ⟫ʷ
wp1432 c4 L = pw1 c4 L (ℓ "乺与临与") (ℓ "与临与乺") tt tt Eq.refl

wp1433 : Base 4 → WsL → ⟪ (ℓ "乫亏") ⟫ʷ ≈ ⟪ (ℓ "亏乫五") ⟫ʷ
wp1433 c4 L = pw3 c4 L (ℓ "乫亏") (ℓ "亏乫五") tt tt Eq.refl

wp1434 : Base 4 → WsL → ⟪ (ℓ "五乫") ⟫ʷ ≈ ⟪ (ℓ "乫五") ⟫ʷ
wp1434 c4 L = pw3 c4 L (ℓ "五乫") (ℓ "乫五") tt tt Eq.refl

wp1435 : Base 4 → WsL → ⟪ (ℓ "亠亓") ⟫ʷ ≈ ⟪ (ℓ "亓五亠") ⟫ʷ
wp1435 c4 L = pw2 c4 L (ℓ "亠亓") (ℓ "亓五亠") tt tt Eq.refl

wp1436 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "亨亪丱亪亨丱") ⟫ʷ
wp1436 c4 L = pw3 c4 L (ℓ "五") (ℓ "亨亪丱亪亨丱") tt tt Eq.refl

wp1437 : Base 4 → WsL → ⟪ (ℓ "五井丱井五丱") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
wp1437 c4 L = pw3 c4 L (ℓ "五井丱井五丱") (ℓ "亨") tt tt Eq.refl

wp1438 : Base 4 → WsL → ⟪ (ℓ "亠些") ⟫ʷ ≈ ⟪ (ℓ "些亜亠") ⟫ʷ
wp1438 c4 L = pw1 c4 L (ℓ "亠些") (ℓ "些亜亠") tt tt Eq.refl

wp1439 : Base 4 → WsL → ⟪ (ℓ "五享") ⟫ʷ ≈ ⟪ (ℓ "享五二") ⟫ʷ
wp1439 c4 L = pw3 c4 L (ℓ "五享") (ℓ "享五二") tt tt Eq.refl

wp1440 : Base 4 → WsL → ⟪ (ℓ "亠亳亘") ⟫ʷ ≈ ⟪ (ℓ "亳亠") ⟫ʷ
wp1440 c4 L = pw1 c4 L (ℓ "亠亳亘") (ℓ "亳亠") tt tt Eq.refl

wp1441 : Base 4 → WsL → ⟪ (ℓ "丯享") ⟫ʷ ≈ ⟪ (ℓ "享丯") ⟫ʷ
wp1441 c4 L = pw3 c4 L (ℓ "丯享") (ℓ "享丯") tt tt Eq.refl

wp1442 : Base 4 → WsL → ⟪ (ℓ "亠与乻") ⟫ʷ ≈ ⟪ (ℓ "与亠") ⟫ʷ
wp1442 c4 L = pw1 c4 L (ℓ "亠与乻") (ℓ "与亠") tt tt Eq.refl

wp1443 : Base 4 → WsL → ⟪ (ℓ "亠乻") ⟫ʷ ≈ ⟪ (ℓ "乻亠") ⟫ʷ
wp1443 c4 L = pw1 c4 L (ℓ "亠乻") (ℓ "乻亠") tt tt Eq.refl

wp1444 : Base 4 → WsL → ⟪ (ℓ "亨与") ⟫ʷ ≈ ⟪ (ℓ "与亨") ⟫ʷ
wp1444 c4 L = pw3 c4 L (ℓ "亨与") (ℓ "与亨") tt tt Eq.refl

wp1445 : Base 4 → WsL → ⟪ (ℓ "丘亣") ⟫ʷ ≈ ⟪ (ℓ "亣丘") ⟫ʷ
wp1445 c4 L = pw1 c4 L (ℓ "丘亣") (ℓ "亣丘") tt tt Eq.refl

wp1446 : Base 4 → WsL → ⟪ (ℓ "丯亣") ⟫ʷ ≈ ⟪ (ℓ "亣丯") ⟫ʷ
wp1446 c4 L = pw1 c4 L (ℓ "丯亣") (ℓ "亣丯") tt tt Eq.refl

wp1447 : Base 4 → WsL → ⟪ (ℓ "丰亣") ⟫ʷ ≈ ⟪ (ℓ "亣丰") ⟫ʷ
wp1447 c4 L = pw1 c4 L (ℓ "丰亣") (ℓ "亣丰") tt tt Eq.refl

wp1448 : Base 4 → WsL → ⟪ (ℓ "丨亣") ⟫ʷ ≈ ⟪ (ℓ "亣丨") ⟫ʷ
wp1448 c4 L = pw2 c4 L (ℓ "丨亣") (ℓ "亣丨") tt tt Eq.refl

wp1449 : Base 4 → WsL → ⟪ (ℓ "丙亣") ⟫ʷ ≈ ⟪ (ℓ "亣丙") ⟫ʷ
wp1449 c4 L = pw1 c4 L (ℓ "丙亣") (ℓ "亣丙") tt tt Eq.refl

wp1450 : Base 4 → WsL → ⟪ (ℓ "亨之亏") ⟫ʷ ≈ ⟪ (ℓ "之亏乗五亨") ⟫ʷ
wp1450 c4 L = pw3 c4 L (ℓ "亨之亏") (ℓ "之亏乗五亨") tt tt Eq.refl

wp1451 : Base 4 → WsL → ⟪ (ℓ "乗亐亣") ⟫ʷ ≈ ⟪ (ℓ "亣乗") ⟫ʷ
wp1451 c4 L = pw2 c4 L (ℓ "乗亐亣") (ℓ "亣乗") tt tt Eq.refl

wp1452 : Base 4 → WsL → ⟪ (ℓ "五亐亣") ⟫ʷ ≈ ⟪ (ℓ "亣五") ⟫ʷ
wp1452 c4 L = pw2 c4 L (ℓ "五亐亣") (ℓ "亣五") tt tt Eq.refl

wp1453 : Base 4 → WsL → ⟪ (ℓ "乗亐五亐") ⟫ʷ ≈ ⟪ (ℓ "乗五") ⟫ʷ
wp1453 c4 L = pw2 c4 L (ℓ "乗亐五亐") (ℓ "乗五") tt tt Eq.refl

wp1454 : Base 4 → WsL → ⟪ (ℓ "亨之亏乗五") ⟫ʷ ≈ ⟪ (ℓ "之亏亨") ⟫ʷ
wp1454 c4 L = pw3 c4 L (ℓ "亨之亏乗五") (ℓ "之亏亨") tt tt Eq.refl

wp1455 : Base 4 → WsL → ⟪ (ℓ "亓乹亓乺与主与") ⟫ʷ ≈ ⟪ (ℓ "与主与亓乹亓乺") ⟫ʷ
wp1455 c4 L = pw2 c4 L (ℓ "亓乹亓乺与主与") (ℓ "与主与亓乹亓乺") tt tt Eq.refl

wp1456 : Base 4 → WsL → ⟪ (ℓ "五亗个") ⟫ʷ ≈ ⟪ (ℓ "亗五") ⟫ʷ
wp1456 c4 L = pw2 c4 L (ℓ "五亗个") (ℓ "亗五") tt tt Eq.refl

wp1457 : Base 4 → WsL → ⟪ (ℓ "五亗") ⟫ʷ ≈ ⟪ (ℓ "亗个五") ⟫ʷ
wp1457 c4 L = pw2 c4 L (ℓ "五亗") (ℓ "亗个五") tt tt Eq.refl

wp1458 : Base 4 → WsL → ⟪ (ℓ "亜亟丱") ⟫ʷ ≈ ⟪ (ℓ "亟亜") ⟫ʷ
wp1458 c4 L = pw3 c4 L (ℓ "亜亟丱") (ℓ "亟亜") tt tt Eq.refl

wp1459 : Base 4 → WsL → ⟪ (ℓ "亜亟") ⟫ʷ ≈ ⟪ (ℓ "亟丱亜") ⟫ʷ
wp1459 c4 L = pw3 c4 L (ℓ "亜亟") (ℓ "亟丱亜") tt tt Eq.refl

wp1460 : Base 4 → WsL → ⟪ (ℓ "亣亚亳") ⟫ʷ ≈ ⟪ (ℓ "亳亚") ⟫ʷ
wp1460 c4 L = pw1 c4 L (ℓ "亣亚亳") (ℓ "亳亚") tt tt Eq.refl

wp1461 : Base 4 → WsL → ⟪ (ℓ "五亣") ⟫ʷ ≈ ⟪ (ℓ "亣亐五") ⟫ʷ
wp1461 c4 L = pw2 c4 L (ℓ "五亣") (ℓ "亣亐五") tt tt Eq.refl

wp1462 : Base 4 → WsL → ⟪ (ℓ "亣亳") ⟫ʷ ≈ ⟪ (ℓ "亳亣") ⟫ʷ
wp1462 c4 L = pw1 c4 L (ℓ "亣亳") (ℓ "亳亣") tt tt Eq.refl

wp1463 : Base 4 → WsL → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "亣亐亣") ⟫ʷ
wp1463 c4 L = pw2 c4 L (ℓ "亐") (ℓ "亣亐亣") tt tt Eq.refl

wp1464 : Base 4 → WsL → ⟪ (ℓ "五亐亯") ⟫ʷ ≈ ⟪ (ℓ "亯五") ⟫ʷ
wp1464 c4 L = pw2 c4 L (ℓ "五亐亯") (ℓ "亯五") tt tt Eq.refl

wp1465 : Base 4 → WsL → ⟪ (ℓ "亏五五") ⟫ʷ ≈ ⟪ (ℓ "亏") ⟫ʷ
wp1465 c4 L = pw3 c4 L (ℓ "亏五五") (ℓ "亏") tt tt Eq.refl

wp1466 : Base 4 → WsL → ⟪ (ℓ "亰些") ⟫ʷ ≈ ⟪ (ℓ "些亜亰") ⟫ʷ
wp1466 c4 L = pw1 c4 L (ℓ "亰些") (ℓ "些亜亰") tt tt Eq.refl

wp1467 : Base 4 → WsL → ⟪ (ℓ "亜亚") ⟫ʷ ≈ ⟪ (ℓ "亚亠亜") ⟫ʷ
wp1467 c4 L = pw1 c4 L (ℓ "亜亚") (ℓ "亚亠亜") tt tt Eq.refl

wp1468 : Base 4 → WsL → ⟪ (ℓ "亠亐亯") ⟫ʷ ≈ ⟪ (ℓ "亯亠") ⟫ʷ
wp1468 c4 L = pw2 c4 L (ℓ "亠亐亯") (ℓ "亯亠") tt tt Eq.refl

wp1469 : Base 4 → WsL → ⟪ (ℓ "亚亠亠") ⟫ʷ ≈ ⟪ (ℓ "亚") ⟫ʷ
wp1469 c4 L = pw1 c4 L (ℓ "亚亠亠") (ℓ "亚") tt tt Eq.refl

wp1470 : Base 4 → WsL → ⟪ (ℓ "举亟") ⟫ʷ ≈ ⟪ (ℓ "亟举丰亜") ⟫ʷ
wp1470 c4 L = pw3 c4 L (ℓ "举亟") (ℓ "亟举丰亜") tt tt Eq.refl

wp1471 : Base 4 → WsL → ⟪ (ℓ "丰亟") ⟫ʷ ≈ ⟪ (ℓ "亟丰") ⟫ʷ
wp1471 c4 L = pw3 c4 L (ℓ "丰亟") (ℓ "亟丰") tt tt Eq.refl

wp1472 : Base 4 → WsL → ⟪ (ℓ "举丰亜丰丱亜") ⟫ʷ ≈ ⟪ (ℓ "举") ⟫ʷ
wp1472 c4 L = pw3 c4 L (ℓ "举丰亜丰丱亜") (ℓ "举") tt tt Eq.refl

wp1473 : Base 4 → WsL → ⟪ (ℓ "丢亟") ⟫ʷ ≈ ⟪ (ℓ "亟丢丯亜") ⟫ʷ
wp1473 c4 L = pw3 c4 L (ℓ "丢亟") (ℓ "亟丢丯亜") tt tt Eq.refl

wp1474 : Base 4 → WsL → ⟪ (ℓ "丯亟") ⟫ʷ ≈ ⟪ (ℓ "亟丯") ⟫ʷ
wp1474 c4 L = pw3 c4 L (ℓ "丯亟") (ℓ "亟丯") tt tt Eq.refl

wp1475 : Base 4 → WsL → ⟪ (ℓ "丢丯亜丯丱亜") ⟫ʷ ≈ ⟪ (ℓ "丢") ⟫ʷ
wp1475 c4 L = pw3 c4 L (ℓ "丢丯亜丯丱亜") (ℓ "丢") tt tt Eq.refl

wp1476 : Base 4 → WsL → ⟪ (ℓ "互与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与互") ⟫ʷ
wp1476 c4 L = pw2 c4 L (ℓ "互与丽与") (ℓ "与丽与互") tt tt Eq.refl

wp1477 : Base 4 → WsL → ⟪ (ℓ "乇与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与乇") ⟫ʷ
wp1477 c4 L = pw3 c4 L (ℓ "乇与丽与") (ℓ "与丽与乇") tt tt Eq.refl

wp1478 : Base 4 → WsL → ⟪ (ℓ "么与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与么") ⟫ʷ
wp1478 c4 L = pw3 c4 L (ℓ "么与丽与") (ℓ "与丽与么") tt tt Eq.refl

wp1479 : Base 4 → WsL → ⟪ (ℓ "亜亘亣") ⟫ʷ ≈ ⟪ (ℓ "亣亜") ⟫ʷ
wp1479 c4 L = pw1 c4 L (ℓ "亜亘亣") (ℓ "亣亜") tt tt Eq.refl

wp1480 : Base 4 → WsL → ⟪ (ℓ "京亣") ⟫ʷ ≈ ⟪ (ℓ "亣京亐") ⟫ʷ
wp1480 c4 L = pw2 c4 L (ℓ "京亣") (ℓ "亣京亐") tt tt Eq.refl

wp1481 : Base 4 → WsL → ⟪ (ℓ "乏亣") ⟫ʷ ≈ ⟪ (ℓ "亣乏") ⟫ʷ
wp1481 c4 L = pw2 c4 L (ℓ "乏亣") (ℓ "亣乏") tt tt Eq.refl

wp1482 : Base 4 → WsL → ⟪ (ℓ "乎亣") ⟫ʷ ≈ ⟪ (ℓ "亣乎") ⟫ʷ
wp1482 c4 L = pw2 c4 L (ℓ "乎亣") (ℓ "亣乎") tt tt Eq.refl

wp1483 : Base 4 → WsL → ⟪ (ℓ "亐亣") ⟫ʷ ≈ ⟪ (ℓ "亣亐") ⟫ʷ
wp1483 c4 L = pw2 c4 L (ℓ "亐亣") (ℓ "亣亐") tt tt Eq.refl

wp1484 : Base 4 → WsL → ⟪ (ℓ "亓亯") ⟫ʷ ≈ ⟪ (ℓ "亯亗亓") ⟫ʷ
wp1484 c4 L = pw2 c4 L (ℓ "亓亯") (ℓ "亯亗亓") tt tt Eq.refl

wp1485 : Base 4 → WsL → ⟪ (ℓ "亜亗二") ⟫ʷ ≈ ⟪ (ℓ "亗亜") ⟫ʷ
wp1485 c4 L = pw3 c4 L (ℓ "亜亗二") (ℓ "亗亜") tt tt Eq.refl

wp1486 : Base 4 → WsL → ⟪ (ℓ "乳互亓乹亓乺") ⟫ʷ ≈ ⟪ (ℓ "亓乹亓乺乳互") ⟫ʷ
wp1486 c4 L = pw2 c4 L (ℓ "乳互亓乹亓乺") (ℓ "亓乹亓乺乳互") tt tt Eq.refl

wp1487 : Base 4 → WsL → ⟪ (ℓ "乳亠互亠") ⟫ʷ ≈ ⟪ (ℓ "乳互") ⟫ʷ
wp1487 c4 L = pw2 c4 L (ℓ "乳亠互亠") (ℓ "乳互") tt tt Eq.refl

wp1488 : Base 4 → WsL → ⟪ (ℓ "临与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与临") ⟫ʷ
wp1488 c4 L = pw3 c4 L (ℓ "临与丽与") (ℓ "与丽与临") tt tt Eq.refl

wp1489 : Base 4 → WsL → ⟪ (ℓ "丰亞") ⟫ʷ ≈ ⟪ (ℓ "亞丰举亜") ⟫ʷ
wp1489 c4 L = pw3 c4 L (ℓ "丰亞") (ℓ "亞丰举亜") tt tt Eq.refl

wp1490 : Base 4 → WsL → ⟪ (ℓ "丰举亜举丿亜") ⟫ʷ ≈ ⟪ (ℓ "丰") ⟫ʷ
wp1490 c4 L = pw3 c4 L (ℓ "丰举亜举丿亜") (ℓ "丰") tt tt Eq.refl

wp1491 : Base 4 → WsL → ⟪ (ℓ "乺丘临上") ⟫ʷ ≈ ⟪ (ℓ "丘临上乺") ⟫ʷ
wp1491 c4 L = pw1 c4 L (ℓ "乺丘临上") (ℓ "丘临上乺") tt tt Eq.refl

wp1492 : Base 4 → WsL → ⟪ (ℓ "乹丘临上") ⟫ʷ ≈ ⟪ (ℓ "丘临上乹") ⟫ʷ
wp1492 c4 L = pw1 c4 L (ℓ "乹丘临上") (ℓ "丘临上乹") tt tt Eq.refl

wp1493 : Base 4 → WsL → ⟪ (ℓ "亜上") ⟫ʷ ≈ ⟪ (ℓ "上亜") ⟫ʷ
wp1493 c4 L = pw1 c4 L (ℓ "亜上") (ℓ "上亜") tt tt Eq.refl

wp1494 : Base 4 → WsL → ⟪ (ℓ "举亗") ⟫ʷ ≈ ⟪ (ℓ "亗举丩五") ⟫ʷ
wp1494 c4 L = pw2 c4 L (ℓ "举亗") (ℓ "亗举丩五") tt tt Eq.refl

wp1495 : Base 4 → WsL → ⟪ (ℓ "丩亗") ⟫ʷ ≈ ⟪ (ℓ "亗丩") ⟫ʷ
wp1495 c4 L = pw2 c4 L (ℓ "丩亗") (ℓ "亗丩") tt tt Eq.refl

wp1496 : Base 4 → WsL → ⟪ (ℓ "举丩五丩个五") ⟫ʷ ≈ ⟪ (ℓ "举") ⟫ʷ
wp1496 c4 L = pw2 c4 L (ℓ "举丩五丩个五") (ℓ "举") tt tt Eq.refl

wp1497 : Base 4 → WsL → ⟪ (ℓ "丢亗") ⟫ʷ ≈ ⟪ (ℓ "亗丢丨五") ⟫ʷ
wp1497 c4 L = pw2 c4 L (ℓ "丢亗") (ℓ "亗丢丨五") tt tt Eq.refl

wp1498 : Base 4 → WsL → ⟪ (ℓ "丨亗") ⟫ʷ ≈ ⟪ (ℓ "亗丨") ⟫ʷ
wp1498 c4 L = pw2 c4 L (ℓ "丨亗") (ℓ "亗丨") tt tt Eq.refl

wp1499 : Base 4 → WsL → ⟪ (ℓ "丢丨五丨个五") ⟫ʷ ≈ ⟪ (ℓ "丢") ⟫ʷ
wp1499 c4 L = pw2 c4 L (ℓ "丢丨五丨个五") (ℓ "丢") tt tt Eq.refl

wp1500 : Base 4 → WsL → ⟪ (ℓ "些与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与些") ⟫ʷ
wp1500 c4 L = pw1 c4 L (ℓ "些与丽与") (ℓ "与丽与些") tt tt Eq.refl

wp1501 : Base 4 → WsL → ⟪ (ℓ "乎与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与乎") ⟫ʷ
wp1501 c4 L = pw2 c4 L (ℓ "乎与丽与") (ℓ "与丽与乎") tt tt Eq.refl

wp1502 : Base 4 → WsL → ⟪ (ℓ "乏与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与乏") ⟫ʷ
wp1502 c4 L = pw2 c4 L (ℓ "乏与丽与") (ℓ "与丽与乏") tt tt Eq.refl

wp1503 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "京亮丸亮京丸") ⟫ʷ
wp1503 c4 L = pw2 c4 L (ℓ "五") (ℓ "京亮丸亮京丸") tt tt Eq.refl

wp1504 : Base 4 → WsL → ⟪ (ℓ "亜亳") ⟫ʷ ≈ ⟪ (ℓ "亳亜亘") ⟫ʷ
wp1504 c4 L = pw1 c4 L (ℓ "亜亳") (ℓ "亳亜亘") tt tt Eq.refl

wp1505 : Base 4 → WsL → ⟪ (ℓ "五亯亐") ⟫ʷ ≈ ⟪ (ℓ "亯五") ⟫ʷ
wp1505 c4 L = pw2 c4 L (ℓ "五亯亐") (ℓ "亯五") tt tt Eq.refl

wp1506 : Base 4 → WsL → ⟪ (ℓ "亠亟") ⟫ʷ ≈ ⟪ (ℓ "亟亠亘") ⟫ʷ
wp1506 c4 L = pw1 c4 L (ℓ "亠亟") (ℓ "亟亠亘") tt tt Eq.refl

wp1507 : Base 4 → WsL → ⟪ (ℓ "亠亘亟") ⟫ʷ ≈ ⟪ (ℓ "亟亠") ⟫ʷ
wp1507 c4 L = pw1 c4 L (ℓ "亠亘亟") (ℓ "亟亠") tt tt Eq.refl

wp1508 : Base 4 → WsL → ⟪ (ℓ "丟亟") ⟫ʷ ≈ ⟪ (ℓ "亟丟") ⟫ʷ
wp1508 c4 L = pw1 c4 L (ℓ "丟亟") (ℓ "亟丟") tt tt Eq.refl

wp1509 : Base 4 → WsL → ⟪ (ℓ "乢亟") ⟫ʷ ≈ ⟪ (ℓ "亟乢") ⟫ʷ
wp1509 c4 L = pw1 c4 L (ℓ "乢亟") (ℓ "亟乢") tt tt Eq.refl

wp1510 : Base 4 → WsL → ⟪ (ℓ "么亟") ⟫ʷ ≈ ⟪ (ℓ "亟么") ⟫ʷ
wp1510 c4 L = pw3 c4 L (ℓ "么亟") (ℓ "亟么") tt tt Eq.refl

wp1511 : Base 4 → WsL → ⟪ (ℓ "丞亟") ⟫ʷ ≈ ⟪ (ℓ "亟丞") ⟫ʷ
wp1511 c4 L = pw1 c4 L (ℓ "丞亟") (ℓ "亟丞") tt tt Eq.refl

wp1512 : Base 4 → WsL → ⟪ (ℓ "二亟") ⟫ʷ ≈ ⟪ (ℓ "亟二") ⟫ʷ
wp1512 c4 L = pw3 c4 L (ℓ "二亟") (ℓ "亟二") tt tt Eq.refl

wp1513 : Base 4 → WsL → ⟪ (ℓ "五亯") ⟫ʷ ≈ ⟪ (ℓ "亯五亐") ⟫ʷ
wp1513 c4 L = pw2 c4 L (ℓ "五亯") (ℓ "亯五亐") tt tt Eq.refl

wp1514 : Base 4 → WsL → ⟪ (ℓ "亜亳亘") ⟫ʷ ≈ ⟪ (ℓ "亳亜") ⟫ʷ
wp1514 c4 L = pw1 c4 L (ℓ "亜亳亘") (ℓ "亳亜") tt tt Eq.refl

wp1515 : Base 4 → WsL → ⟪ (ℓ "五亣") ⟫ʷ ≈ ⟪ (ℓ "亣五亐") ⟫ʷ
wp1515 c4 L = pw2 c4 L (ℓ "五亣") (ℓ "亣五亐") tt tt Eq.refl

wp1516 : Base 4 → WsL → ⟪ (ℓ "乪书些") ⟫ʷ ≈ ⟪ (ℓ "书些乪") ⟫ʷ
wp1516 c4 L = pw1 c4 L (ℓ "乪书些") (ℓ "书些乪") tt tt Eq.refl

wp1517 : Base 4 → WsL → ⟪ (ℓ "乩书些") ⟫ʷ ≈ ⟪ (ℓ "书些乩") ⟫ʷ
wp1517 c4 L = pw1 c4 L (ℓ "乩书些") (ℓ "书些乩") tt tt Eq.refl

wp1518 : Base 4 → WsL → ⟪ (ℓ "主与丽与") ⟫ʷ ≈ ⟪ (ℓ "与丽与主") ⟫ʷ
wp1518 c4 L = pw1 c4 L (ℓ "主与丽与") (ℓ "与丽与主") tt tt Eq.refl

wp1519 : Base 4 → WsL → ⟪ (ℓ "丞主上亓乹亓乺") ⟫ʷ ≈ ⟪ (ℓ "亓乹亓乺丞主上") ⟫ʷ
wp1519 c4 L = pw2 c4 L (ℓ "丞主上亓乹亓乺") (ℓ "亓乹亓乺丞主上") tt tt Eq.refl

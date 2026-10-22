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

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp1353 : Base 4 → WsL → ⟪ (X0 ∷ CZ14 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wp1353 c4 L = pw2 c4 L (X0 ∷ CZ14 ∷ CZ14 ∷ []) (X0 ∷ []) tt tt Eq.refl

wp1354 : Base 4 → WsL → ⟪ (Toff302 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) ⟫ʷ
wp1354 c4 L = pw1 c4 L (Toff302 ∷ Toff423 ∷ []) (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) tt tt Eq.refl

wp1355 : Base 4 → WsL → ⟪ (CS02⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS02⁻ ∷ []) ⟫ʷ
wp1355 c4 L = pw1 c4 L (CS02⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp1356 : Base 4 → WsL → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ012 ∷ Toff402 ∷ []) ⟫ʷ
wp1356 c4 L = pw3 c4 L (CCZ012 ∷ []) (Toff402 ∷ CCZ012 ∷ Toff402 ∷ []) tt tt Eq.refl

wp1357 : Base 4 → WsL → ⟪ (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff302 ∷ []) ⟫ʷ
wp1357 c4 L = pw1 c4 L (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (Toff423 ∷ Toff302 ∷ []) tt tt Eq.refl

wp1358 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ []) ⟫ʷ
wp1358 c4 L = pw3 c4 L (CCZ014 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1359 : Base 4 → WsL → ⟪ (Toff402 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ Toff402 ∷ []) ⟫ʷ
wp1359 c4 L = pw3 c4 L (Toff402 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff402 ∷ []) tt tt Eq.refl

wp1360 : Base 4 → WsL → ⟪ (CCZ014 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CCZ014 ∷ []) ⟫ʷ
wp1360 c4 L = pw2 c4 L (CCZ014 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1361 : Base 4 → WsL → ⟪ (Toff413 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ Toff413 ∷ []) ⟫ʷ
wp1361 c4 L = pw2 c4 L (Toff413 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff413 ∷ []) tt tt Eq.refl

wp1362 : Base 4 → WsL → ⟪ (Toff413 ∷ ι ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ Toff413 ∷ []) ⟫ʷ
wp1362 c4 L = pw2 c4 L (Toff413 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff413 ∷ []) tt tt Eq.refl

wp1363 : Base 4 → WsL → ⟪ (CCZ024 ∷ K2 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CK02 ∷ S0 ∷ CCZ024 ∷ []) ⟫ʷ
wp1363 c4 L = pw3 c4 L (CCZ024 ∷ K2 ∷ CK02 ∷ S0 ∷ []) (K2 ∷ CK02 ∷ S0 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1364 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff103 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ014 ∷ []) ⟫ʷ
wp1364 c4 L = pw2 c4 L (CCZ014 ∷ Toff103 ∷ CCZ034 ∷ []) (Toff103 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1365 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ034 ∷ CCZ023 ∷ []) ⟫ʷ
wp1365 c4 L = pw1 c4 L (CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ034 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1366 : Base 4 → WsL → ⟪ (Toff103 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ []) ⟫ʷ
wp1366 c4 L = pw2 c4 L (Toff103 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff103 ∷ []) tt tt Eq.refl

wp1367 : Base 4 → WsL → ⟪ (CCZ023 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ023 ∷ []) ⟫ʷ
wp1367 c4 L = pw1 c4 L (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1368 : Base 4 → WsL → ⟪ (CCZ234 ∷ CX23 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ []) ⟫ʷ
wp1368 c4 L = pw1 c4 L (CCZ234 ∷ CX23 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1369 : Base 4 → WsL → ⟪ (CZ24 ∷ CCZ012 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CZ24 ∷ []) ⟫ʷ
wp1369 c4 L = pw3 c4 L (CZ24 ∷ CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CZ24 ∷ []) tt tt Eq.refl

wp1370 : Base 4 → WsL → ⟪ (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ024 ∷ []) ⟫ʷ
wp1370 c4 L = pw3 c4 L (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1371 : Base 4 → WsL → ⟪ (CZ24 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ CCZ024 ∷ []) ⟫ʷ
wp1371 c4 L = pw3 c4 L (CZ24 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (CZ24 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1372 : Base 4 → WsL → ⟪ (CCZ234 ∷ CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff302 ∷ CCZ234 ∷ []) ⟫ʷ
wp1372 c4 L = pw1 c4 L (CCZ234 ∷ CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ []) (CX23 ∷ Toff302 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1373 : Base 4 → WsL → ⟪ (Toff103 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) ⟫ʷ
wp1373 c4 L = pw2 c4 L (Toff103 ∷ Toff413 ∷ []) (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) tt tt Eq.refl

wp1374 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ024 ∷ []) ⟫ʷ
wp1374 c4 L = pw1 c4 L (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (Toff403 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1375 : Base 4 → WsL → ⟪ (CS03⁻ ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS03⁻ ∷ []) ⟫ʷ
wp1375 c4 L = pw2 c4 L (CS03⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp1376 : Base 4 → WsL → ⟪ (CS03 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS03 ∷ []) ⟫ʷ
wp1376 c4 L = pw2 c4 L (CS03 ∷ Toff413 ∷ []) (Toff413 ∷ CS03 ∷ []) tt tt Eq.refl

wp1377 : Base 4 → WsL → ⟪ (Toff403 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff403 ∷ []) ⟫ʷ
wp1377 c4 L = pw2 c4 L (Toff403 ∷ Toff413 ∷ []) (Toff413 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1378 : Base 4 → WsL → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ023 ∷ Toff403 ∷ []) ⟫ʷ
wp1378 c4 L = pw1 c4 L (CCZ023 ∷ []) (Toff403 ∷ CCZ023 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1379 : Base 4 → WsL → ⟪ (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff103 ∷ []) ⟫ʷ
wp1379 c4 L = pw2 c4 L (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (Toff413 ∷ Toff103 ∷ []) tt tt Eq.refl

wp1380 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ023 ∷ CCZ024 ∷ []) ⟫ʷ
wp1380 c4 L = pw1 c4 L (CCZ024 ∷ CX34 ∷ []) (CX34 ∷ CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1381 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) ⟫ʷ
wp1381 c4 L = pw1 c4 L (CCZ024 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1382 : Base 4 → WsL → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ023 ∷ CX34 ∷ []) ⟫ʷ
wp1382 c4 L = pw1 c4 L (CCZ023 ∷ []) (CX34 ∷ CCZ023 ∷ CX34 ∷ []) tt tt Eq.refl

wp1383 : Base 4 → WsL → ⟪ (CCZ014 ∷ ι ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp1383 c4 L = pw2 c4 L (CCZ014 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1384 : Base 4 → WsL → ⟪ (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ []) ⟫ʷ
wp1384 c4 L = pw1 c4 L (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1385 : Base 4 → WsL → ⟪ (CCZ124 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ124 ∷ CCZ012 ∷ []) ⟫ʷ
wp1385 c4 L = pw3 c4 L (CCZ124 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ124 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1386 : Base 4 → WsL → ⟪ (CX32 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CX32 ∷ Toff403 ∷ []) ⟫ʷ
wp1386 c4 L = pw1 c4 L (CX32 ∷ Toff402 ∷ []) (Toff402 ∷ CX32 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1387 : Base 4 → WsL → ⟪ (CCZ134 ∷ Toff403 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ134 ∷ []) ⟫ʷ
wp1387 c4 L = pw2 c4 L (CCZ134 ∷ Toff403 ∷ CCZ013 ∷ []) (Toff403 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1388 : Base 4 → WsL → ⟪ (CS01 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS01 ∷ []) ⟫ʷ
wp1388 c4 L = pw3 c4 L (CS01 ∷ Toff402 ∷ []) (Toff402 ∷ CS01 ∷ []) tt tt Eq.refl

wp1389 : Base 4 → WsL → ⟪ (Toff402 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff402 ∷ []) ⟫ʷ
wp1389 c4 L = pw1 c4 L (Toff402 ∷ Toff403 ∷ []) (Toff403 ∷ Toff402 ∷ []) tt tt Eq.refl

wp1390 : Base 4 → WsL → ⟪ (CX32 ∷ Toff403 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
wp1390 c4 L = pw1 c4 L (CX32 ∷ Toff403 ∷ Toff403 ∷ []) (CX32 ∷ []) tt tt Eq.refl

wp1391 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) ⟫ʷ
wp1391 c4 L = pw1 c4 L (CCZ034 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) tt tt Eq.refl

wp1392 : Base 4 → WsL → ⟪ (CCZ034 ∷ CZ03 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ []) ⟫ʷ
wp1392 c4 L = pw1 c4 L (CCZ034 ∷ CZ03 ∷ Toff403 ∷ CCZ034 ∷ []) (Toff403 ∷ []) tt tt Eq.refl

wp1393 : Base 4 → WsL → ⟪ (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ K3 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ
wp1393 c4 L = pw1 c4 L (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) (Toff403 ∷ K3 ∷ CK03 ∷ S0 ∷ []) tt tt Eq.refl

wp1394 : Base 4 → WsL → ⟪ (Toff401 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ Toff401 ∷ []) ⟫ʷ
wp1394 c4 L = pw2 c4 L (Toff401 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff401 ∷ []) tt tt Eq.refl

wp1395 : Base 4 → WsL → ⟪ (CCZ014 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CCZ014 ∷ []) ⟫ʷ
wp1395 c4 L = pw2 c4 L (CCZ014 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1396 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ034 ∷ CCZ013 ∷ []) ⟫ʷ
wp1396 c4 L = pw2 c4 L (CCZ034 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1397 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff412 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ024 ∷ []) ⟫ʷ
wp1397 c4 L = pw3 c4 L (CCZ024 ∷ Toff412 ∷ CCZ012 ∷ []) (Toff412 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1398 : Base 4 → WsL → ⟪ (CS01 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS01 ∷ []) ⟫ʷ
wp1398 c4 L = pw2 c4 L (CS01 ∷ Toff413 ∷ []) (Toff413 ∷ CS01 ∷ []) tt tt Eq.refl

wp1399 : Base 4 → WsL → ⟪ (CCZ034 ∷ CZ03 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
wp1399 c4 L = pw1 c4 L (CCZ034 ∷ CZ03 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1400 : Base 4 → WsL → ⟪ (CCZ034 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff403 ∷ []) ⟫ʷ
wp1400 c4 L = pw1 c4 L (CCZ034 ∷ CZ03 ∷ []) (Toff403 ∷ CCZ034 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1401 : Base 4 → WsL → ⟪ (CX01 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CX01 ∷ []) ⟫ʷ
wp1401 c4 L = pw2 c4 L (CX01 ∷ Toff403 ∷ []) (Toff403 ∷ CX01 ∷ []) tt tt Eq.refl

wp1402 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ024 ∷ CCZ023 ∷ []) ⟫ʷ
wp1402 c4 L = pw1 c4 L (CCZ024 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ024 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1403 : Base 4 → WsL → ⟪ (CX10 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CX10 ∷ Toff413 ∷ []) ⟫ʷ
wp1403 c4 L = pw2 c4 L (CX10 ∷ Toff403 ∷ []) (Toff403 ∷ CX10 ∷ Toff413 ∷ []) tt tt Eq.refl

wp1404 : Base 4 → WsL → ⟪ (CS23 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS23 ∷ []) ⟫ʷ
wp1404 c4 L = pw1 c4 L (CS23 ∷ Toff403 ∷ []) (Toff403 ∷ CS23 ∷ []) tt tt Eq.refl

wp1405 : Base 4 → WsL → ⟪ (CX31 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CX31 ∷ []) ⟫ʷ
wp1405 c4 L = pw2 c4 L (CX31 ∷ Toff403 ∷ []) (Toff403 ∷ CX31 ∷ []) tt tt Eq.refl

wp1406 : Base 4 → WsL → ⟪ (CX10 ∷ Toff413 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wp1406 c4 L = pw2 c4 L (CX10 ∷ Toff413 ∷ Toff413 ∷ []) (CX10 ∷ []) tt tt Eq.refl

wp1407 : Base 4 → WsL → ⟪ (CX10 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX10 ∷ []) ⟫ʷ
wp1407 c4 L = pw2 c4 L (CX10 ∷ Toff413 ∷ []) (Toff413 ∷ CX10 ∷ []) tt tt Eq.refl

wp1408 : Base 4 → WsL → ⟪ (CX01 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX01 ∷ Toff403 ∷ []) ⟫ʷ
wp1408 c4 L = pw2 c4 L (CX01 ∷ Toff413 ∷ []) (Toff413 ∷ CX01 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1409 : Base 4 → WsL → ⟪ (CX30 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX30 ∷ []) ⟫ʷ
wp1409 c4 L = pw2 c4 L (CX30 ∷ Toff413 ∷ []) (Toff413 ∷ CX30 ∷ []) tt tt Eq.refl

wp1410 : Base 4 → WsL → ⟪ (CX01 ∷ Toff403 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
wp1410 c4 L = pw2 c4 L (CX01 ∷ Toff403 ∷ Toff403 ∷ []) (CX01 ∷ []) tt tt Eq.refl

wp1411 : Base 4 → WsL → ⟪ (CCZ024 ∷ CCZ034 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ024 ∷ []) ⟫ʷ
wp1411 c4 L = pw1 c4 L (CCZ024 ∷ CCZ034 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1412 : Base 4 → WsL → ⟪ (CCZ013 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ013 ∷ []) ⟫ʷ
wp1412 c4 L = pw2 c4 L (CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1413 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ024 ∷ CCZ012 ∷ []) ⟫ʷ
wp1413 c4 L = pw3 c4 L (CCZ024 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1414 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff413 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ034 ∷ []) ⟫ʷ
wp1414 c4 L = pw2 c4 L (CCZ034 ∷ Toff413 ∷ CCZ013 ∷ []) (Toff413 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1415 : Base 4 → WsL → ⟪ (CS01 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS01 ∷ []) ⟫ʷ
wp1415 c4 L = pw3 c4 L (CS01 ∷ Toff412 ∷ []) (Toff412 ∷ CS01 ∷ []) tt tt Eq.refl

wp1416 : Base 4 → WsL → ⟪ (CCZ024 ∷ CZ02 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ024 ∷ []) ⟫ʷ
wp1416 c4 L = pw3 c4 L (CCZ024 ∷ CZ02 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1417 : Base 4 → WsL → ⟪ (CCZ024 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ024 ∷ Toff402 ∷ []) ⟫ʷ
wp1417 c4 L = pw3 c4 L (CCZ024 ∷ CZ02 ∷ []) (Toff402 ∷ CCZ024 ∷ Toff402 ∷ []) tt tt Eq.refl

wp1418 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ024 ∷ CZ02 ∷ []) ⟫ʷ
wp1418 c4 L = pw3 c4 L (CCZ024 ∷ []) (CZ02 ∷ CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl

wp1419 : Base 4 → WsL → ⟪ (CCZ134 ∷ Toff103 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) ⟫ʷ
wp1419 c4 L = pw2 c4 L (CCZ134 ∷ Toff103 ∷ CCZ034 ∷ []) (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1420 : Base 4 → WsL → ⟪ (CCZ134 ∷ CCZ034 ∷ Toff103 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ
wp1420 c4 L = pw2 c4 L (CCZ134 ∷ CCZ034 ∷ Toff103 ∷ CCZ034 ∷ []) (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1421 : Base 4 → WsL → ⟪ (CCZ134 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ134 ∷ []) ⟫ʷ
wp1421 c4 L = pw2 c4 L (CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1422 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ034 ∷ []) ⟫ʷ
wp1422 c4 L = pw2 c4 L (CCZ034 ∷ Toff103 ∷ []) (Toff103 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1423 : Base 4 → WsL → ⟪ (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff301 ∷ []) ⟫ʷ
wp1423 c4 L = pw2 c4 L (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) (Toff413 ∷ Toff301 ∷ []) tt tt Eq.refl

wp1424 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ012 ∷ CCZ024 ∷ []) ⟫ʷ
wp1424 c4 L = pw3 c4 L (CCZ024 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1425 : Base 4 → WsL → ⟪ (Toff401 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff401 ∷ []) ⟫ʷ
wp1425 c4 L = pw2 c4 L (Toff401 ∷ Toff413 ∷ []) (Toff413 ∷ Toff401 ∷ []) tt tt Eq.refl

wp1426 : Base 4 → WsL → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ012 ∷ Toff401 ∷ []) ⟫ʷ
wp1426 c4 L = pw3 c4 L (CCZ012 ∷ []) (Toff401 ∷ CCZ012 ∷ Toff401 ∷ []) tt tt Eq.refl

wp1427 : Base 4 → WsL → ⟪ (CS34 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS34 ∷ []) ⟫ʷ
wp1427 c4 L = pw2 c4 L (CS34 ∷ Toff103 ∷ []) (Toff103 ∷ CS34 ∷ []) tt tt Eq.refl

wp1428 : Base 4 → WsL → ⟪ (CS34⁻ ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS34⁻ ∷ []) ⟫ʷ
wp1428 c4 L = pw2 c4 L (CS34⁻ ∷ Toff103 ∷ []) (Toff103 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1429 : Base 4 → WsL → ⟪ (CS02 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS02 ∷ CS04 ∷ CCZ024 ∷ []) ⟫ʷ
wp1429 c4 L = pw3 c4 L (CS02 ∷ Toff204 ∷ []) (Toff204 ∷ CS02 ∷ CS04 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1430 : Base 4 → WsL → ⟪ (CS02 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
wp1430 c4 L = pw3 c4 L (CS02 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) (CS02 ∷ []) tt tt Eq.refl

wp1431 : Base 4 → WsL → ⟪ (CS34 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CS34 ∷ []) ⟫ʷ
wp1431 c4 L = pw1 c4 L (CS34 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CS34 ∷ []) tt tt Eq.refl

wp1432 : Base 4 → WsL → ⟪ (CS34⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CS34⁻ ∷ []) ⟫ʷ
wp1432 c4 L = pw1 c4 L (CS34⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1433 : Base 4 → WsL → ⟪ (CZ24 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CZ24 ∷ CCZ014 ∷ []) ⟫ʷ
wp1433 c4 L = pw3 c4 L (CZ24 ∷ Toff201 ∷ []) (Toff201 ∷ CZ24 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1434 : Base 4 → WsL → ⟪ (CCZ014 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ CCZ014 ∷ []) ⟫ʷ
wp1434 c4 L = pw3 c4 L (CCZ014 ∷ CZ24 ∷ []) (CZ24 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1435 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ014 ∷ CCZ034 ∷ []) ⟫ʷ
wp1435 c4 L = pw2 c4 L (CCZ034 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1436 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) ⟫ʷ
wp1436 c4 L = pw3 c4 L (CCZ014 ∷ []) (CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) tt tt Eq.refl

wp1437 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wp1437 c4 L = pw3 c4 L (CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wp1438 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) ⟫ʷ
wp1438 c4 L = pw1 c4 L (CCZ034 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1439 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ014 ∷ CCZ012 ∷ []) ⟫ʷ
wp1439 c4 L = pw3 c4 L (CCZ014 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1440 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff423 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ034 ∷ []) ⟫ʷ
wp1440 c4 L = pw1 c4 L (CCZ034 ∷ Toff423 ∷ CCZ023 ∷ []) (Toff423 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1441 : Base 4 → WsL → ⟪ (CS02 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS02 ∷ []) ⟫ʷ
wp1441 c4 L = pw3 c4 L (CS02 ∷ Toff412 ∷ []) (Toff412 ∷ CS02 ∷ []) tt tt Eq.refl

wp1442 : Base 4 → WsL → ⟪ (CCZ034 ∷ X0 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ034 ∷ []) ⟫ʷ
wp1442 c4 L = pw1 c4 L (CCZ034 ∷ X0 ∷ CZ34 ∷ []) (X0 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1443 : Base 4 → WsL → ⟪ (CCZ034 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CZ34 ∷ CCZ034 ∷ []) ⟫ʷ
wp1443 c4 L = pw1 c4 L (CCZ034 ∷ CZ34 ∷ []) (CZ34 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1444 : Base 4 → WsL → ⟪ (CCZ124 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ124 ∷ []) ⟫ʷ
wp1444 c4 L = pw3 c4 L (CCZ124 ∷ X0 ∷ []) (X0 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1445 : Base 4 → WsL → ⟪ (K2 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ K2 ∷ []) ⟫ʷ
wp1445 c4 L = pw1 c4 L (K2 ∷ Toff403 ∷ []) (Toff403 ∷ K2 ∷ []) tt tt Eq.refl

wp1446 : Base 4 → WsL → ⟪ (CS02 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS02 ∷ []) ⟫ʷ
wp1446 c4 L = pw1 c4 L (CS02 ∷ Toff403 ∷ []) (Toff403 ∷ CS02 ∷ []) tt tt Eq.refl

wp1447 : Base 4 → WsL → ⟪ (CS02⁻ ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS02⁻ ∷ []) ⟫ʷ
wp1447 c4 L = pw1 c4 L (CS02⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp1448 : Base 4 → WsL → ⟪ (CS01 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS01 ∷ []) ⟫ʷ
wp1448 c4 L = pw2 c4 L (CS01 ∷ Toff403 ∷ []) (Toff403 ∷ CS01 ∷ []) tt tt Eq.refl

wp1449 : Base 4 → WsL → ⟪ (K2⁻ ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ K2⁻ ∷ []) ⟫ʷ
wp1449 c4 L = pw1 c4 L (K2⁻ ∷ Toff403 ∷ []) (Toff403 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp1450 : Base 4 → WsL → ⟪ (CCZ124 ∷ CX12 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ []) ⟫ʷ
wp1450 c4 L = pw3 c4 L (CCZ124 ∷ CX12 ∷ Toff201 ∷ []) (CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1451 : Base 4 → WsL → ⟪ (CZ14 ∷ CCZ013 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CZ14 ∷ []) ⟫ʷ
wp1451 c4 L = pw2 c4 L (CZ14 ∷ CCZ013 ∷ Toff403 ∷ []) (Toff403 ∷ CZ14 ∷ []) tt tt Eq.refl

wp1452 : Base 4 → WsL → ⟪ (CCZ014 ∷ CCZ013 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ014 ∷ []) ⟫ʷ
wp1452 c4 L = pw2 c4 L (CCZ014 ∷ CCZ013 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1453 : Base 4 → WsL → ⟪ (CZ14 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ CCZ014 ∷ []) ⟫ʷ
wp1453 c4 L = pw2 c4 L (CZ14 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) (CZ14 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1454 : Base 4 → WsL → ⟪ (CCZ124 ∷ CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff201 ∷ CCZ124 ∷ []) ⟫ʷ
wp1454 c4 L = pw3 c4 L (CCZ124 ∷ CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ []) (CX12 ∷ Toff201 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1455 : Base 4 → WsL → ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ
wp1455 c4 L = pw2 c4 L (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1456 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff401 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ014 ∷ []) ⟫ʷ
wp1456 c4 L = pw2 c4 L (CCZ014 ∷ Toff401 ∷ CZ01 ∷ []) (Toff401 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1457 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CZ01 ∷ CCZ014 ∷ []) ⟫ʷ
wp1457 c4 L = pw2 c4 L (CCZ014 ∷ Toff401 ∷ []) (Toff401 ∷ CZ01 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1458 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff402 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ024 ∷ []) ⟫ʷ
wp1458 c4 L = pw3 c4 L (CCZ024 ∷ Toff402 ∷ CZ02 ∷ []) (Toff402 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1459 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CZ02 ∷ CCZ024 ∷ []) ⟫ʷ
wp1459 c4 L = pw3 c4 L (CCZ024 ∷ Toff402 ∷ []) (Toff402 ∷ CZ02 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1460 : Base 4 → WsL → ⟪ (Toff403 ∷ Toff203 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff203 ∷ []) ⟫ʷ
wp1460 c4 L = pw1 c4 L (Toff403 ∷ Toff203 ∷ Toff423 ∷ []) (Toff423 ∷ Toff203 ∷ []) tt tt Eq.refl

wp1461 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ013 ∷ CCZ014 ∷ []) ⟫ʷ
wp1461 c4 L = pw2 c4 L (CCZ014 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ013 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1462 : Base 4 → WsL → ⟪ (Toff403 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff403 ∷ []) ⟫ʷ
wp1462 c4 L = pw1 c4 L (Toff403 ∷ Toff423 ∷ []) (Toff423 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1463 : Base 4 → WsL → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ013 ∷ Toff403 ∷ []) ⟫ʷ
wp1463 c4 L = pw2 c4 L (CCZ013 ∷ []) (Toff403 ∷ CCZ013 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1464 : Base 4 → WsL → ⟪ (CCZ014 ∷ CCZ013 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ014 ∷ []) ⟫ʷ
wp1464 c4 L = pw2 c4 L (CCZ014 ∷ CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1465 : Base 4 → WsL → ⟪ (Toff201 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
wp1465 c4 L = pw3 c4 L (Toff201 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff201 ∷ []) tt tt Eq.refl

wp1466 : Base 4 → WsL → ⟪ (CCZ234 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) ⟫ʷ
wp1466 c4 L = pw1 c4 L (CCZ234 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1467 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ
wp1467 c4 L = pw1 c4 L (CCZ024 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1468 : Base 4 → WsL → ⟪ (CCZ034 ∷ CCZ013 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ034 ∷ []) ⟫ʷ
wp1468 c4 L = pw2 c4 L (CCZ034 ∷ CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1469 : Base 4 → WsL → ⟪ (Toff203 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
wp1469 c4 L = pw1 c4 L (Toff203 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff203 ∷ []) tt tt Eq.refl

wp1470 : Base 4 → WsL → ⟪ (CS04⁻ ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS04⁻ ∷ CS02⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp1470 c4 L = pw3 c4 L (CS04⁻ ∷ Toff402 ∷ []) (Toff402 ∷ CS04⁻ ∷ CS02⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1471 : Base 4 → WsL → ⟪ (CS02⁻ ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS02⁻ ∷ []) ⟫ʷ
wp1471 c4 L = pw3 c4 L (CS02⁻ ∷ Toff402 ∷ []) (Toff402 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp1472 : Base 4 → WsL → ⟪ (CS04⁻ ∷ CS02⁻ ∷ CCZ024 ∷ CS02⁻ ∷ CZ02 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ []) ⟫ʷ
wp1472 c4 L = pw3 c4 L (CS04⁻ ∷ CS02⁻ ∷ CCZ024 ∷ CS02⁻ ∷ CZ02 ∷ CCZ024 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl

wp1473 : Base 4 → WsL → ⟪ (S4 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ S4 ∷ CS02 ∷ CCZ024 ∷ []) ⟫ʷ
wp1473 c4 L = pw3 c4 L (S4 ∷ Toff402 ∷ []) (Toff402 ∷ S4 ∷ CS02 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1474 : Base 4 → WsL → ⟪ (CS02 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS02 ∷ []) ⟫ʷ
wp1474 c4 L = pw3 c4 L (CS02 ∷ Toff402 ∷ []) (Toff402 ∷ CS02 ∷ []) tt tt Eq.refl

wp1475 : Base 4 → WsL → ⟪ (S4 ∷ CS02 ∷ CCZ024 ∷ CS02 ∷ CZ02 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ []) ⟫ʷ
wp1475 c4 L = pw3 c4 L (S4 ∷ CS02 ∷ CCZ024 ∷ CS02 ∷ CZ02 ∷ CCZ024 ∷ []) (S4 ∷ []) tt tt Eq.refl

wp1476 : Base 4 → WsL → ⟪ (Toff103 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ Toff103 ∷ []) ⟫ʷ
wp1476 c4 L = pw2 c4 L (Toff103 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ Toff103 ∷ []) tt tt Eq.refl

wp1477 : Base 4 → WsL → ⟪ (CS12 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS12 ∷ []) ⟫ʷ
wp1477 c4 L = pw3 c4 L (CS12 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS12 ∷ []) tt tt Eq.refl

wp1478 : Base 4 → WsL → ⟪ (CS12⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS12⁻ ∷ []) ⟫ʷ
wp1478 c4 L = pw3 c4 L (CS12⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp1479 : Base 4 → WsL → ⟪ (CCZ024 ∷ CCZ023 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ024 ∷ []) ⟫ʷ
wp1479 c4 L = pw1 c4 L (CCZ024 ∷ CCZ023 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1480 : Base 4 → WsL → ⟪ (CCZ134 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ134 ∷ CCZ013 ∷ []) ⟫ʷ
wp1480 c4 L = pw2 c4 L (CCZ134 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ134 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1481 : Base 4 → WsL → ⟪ (CS13⁻ ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS13⁻ ∷ []) ⟫ʷ
wp1481 c4 L = pw2 c4 L (CS13⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp1482 : Base 4 → WsL → ⟪ (CS13 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS13 ∷ []) ⟫ʷ
wp1482 c4 L = pw2 c4 L (CS13 ∷ Toff403 ∷ []) (Toff403 ∷ CS13 ∷ []) tt tt Eq.refl

wp1483 : Base 4 → WsL → ⟪ (CCZ013 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ013 ∷ []) ⟫ʷ
wp1483 c4 L = pw2 c4 L (CCZ013 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1484 : Base 4 → WsL → ⟪ (Toff301 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff401 ∷ Toff301 ∷ []) ⟫ʷ
wp1484 c4 L = pw2 c4 L (Toff301 ∷ Toff413 ∷ []) (Toff413 ∷ Toff401 ∷ Toff301 ∷ []) tt tt Eq.refl

wp1485 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff401 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ024 ∷ []) ⟫ʷ
wp1485 c4 L = pw3 c4 L (CCZ024 ∷ Toff401 ∷ CCZ012 ∷ []) (Toff401 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1486 : Base 4 → WsL → ⟪ (CX31 ∷ Toff103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX31 ∷ Toff103 ∷ []) ⟫ʷ
wp1486 c4 L = pw2 c4 L (CX31 ∷ Toff103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX31 ∷ Toff103 ∷ []) tt tt Eq.refl

wp1487 : Base 4 → WsL → ⟪ (CX31 ∷ CCZ034 ∷ Toff103 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Toff103 ∷ []) ⟫ʷ
wp1487 c4 L = pw2 c4 L (CX31 ∷ CCZ034 ∷ Toff103 ∷ CCZ034 ∷ []) (CX31 ∷ Toff103 ∷ []) tt tt Eq.refl

wp1488 : Base 4 → WsL → ⟪ (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ
wp1488 c4 L = pw3 c4 L (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CK02 ∷ []) tt tt Eq.refl

wp1489 : Base 4 → WsL → ⟪ (CS02⁻ ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS02⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp1489 c4 L = pw3 c4 L (CS02⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS02⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1490 : Base 4 → WsL → ⟪ (CS02⁻ ∷ CS04⁻ ∷ CCZ024 ∷ CS04⁻ ∷ CZ04 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wp1490 c4 L = pw3 c4 L (CS02⁻ ∷ CS04⁻ ∷ CCZ024 ∷ CS04⁻ ∷ CZ04 ∷ CCZ024 ∷ []) (CS02⁻ ∷ []) tt tt Eq.refl

wp1491 : Base 4 → WsL → ⟪ (CS34⁻ ∷ K2 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CK02 ∷ S0 ∷ CS34⁻ ∷ []) ⟫ʷ
wp1491 c4 L = pw1 c4 L (CS34⁻ ∷ K2 ∷ CK02 ∷ S0 ∷ []) (K2 ∷ CK02 ∷ S0 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1492 : Base 4 → WsL → ⟪ (CS34 ∷ K2 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CK02 ∷ S0 ∷ CS34 ∷ []) ⟫ʷ
wp1492 c4 L = pw1 c4 L (CS34 ∷ K2 ∷ CK02 ∷ S0 ∷ []) (K2 ∷ CK02 ∷ S0 ∷ CS34 ∷ []) tt tt Eq.refl

wp1493 : Base 4 → WsL → ⟪ (CCZ024 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CCZ024 ∷ []) ⟫ʷ
wp1493 c4 L = pw1 c4 L (CCZ024 ∷ S0 ∷ []) (S0 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1494 : Base 4 → WsL → ⟪ (CS04⁻ ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp1494 c4 L = pw2 c4 L (CS04⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1495 : Base 4 → WsL → ⟪ (CS01⁻ ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS01⁻ ∷ []) ⟫ʷ
wp1495 c4 L = pw2 c4 L (CS01⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp1496 : Base 4 → WsL → ⟪ (CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ CS01⁻ ∷ CZ01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ []) ⟫ʷ
wp1496 c4 L = pw2 c4 L (CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ CS01⁻ ∷ CZ01 ∷ CCZ014 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl

wp1497 : Base 4 → WsL → ⟪ (S4 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ S4 ∷ CS01 ∷ CCZ014 ∷ []) ⟫ʷ
wp1497 c4 L = pw2 c4 L (S4 ∷ Toff401 ∷ []) (Toff401 ∷ S4 ∷ CS01 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1498 : Base 4 → WsL → ⟪ (CS01 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS01 ∷ []) ⟫ʷ
wp1498 c4 L = pw2 c4 L (CS01 ∷ Toff401 ∷ []) (Toff401 ∷ CS01 ∷ []) tt tt Eq.refl

wp1499 : Base 4 → WsL → ⟪ (S4 ∷ CS01 ∷ CCZ014 ∷ CS01 ∷ CZ01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ []) ⟫ʷ
wp1499 c4 L = pw2 c4 L (S4 ∷ CS01 ∷ CCZ014 ∷ CS01 ∷ CZ01 ∷ CCZ014 ∷ []) (S4 ∷ []) tt tt Eq.refl

wp1500 : Base 4 → WsL → ⟪ (Toff302 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ Toff302 ∷ []) ⟫ʷ
wp1500 c4 L = pw1 c4 L (Toff302 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ Toff302 ∷ []) tt tt Eq.refl

wp1501 : Base 4 → WsL → ⟪ (CS13 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS13 ∷ []) ⟫ʷ
wp1501 c4 L = pw2 c4 L (CS13 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS13 ∷ []) tt tt Eq.refl

wp1502 : Base 4 → WsL → ⟪ (CS13⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS13⁻ ∷ []) ⟫ʷ
wp1502 c4 L = pw2 c4 L (CS13⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp1503 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ []) ⟫ʷ
wp1503 c4 L = pw2 c4 L (CCZ014 ∷ []) (CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ []) tt tt Eq.refl

wp1504 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ024 ∷ CCZ023 ∷ []) ⟫ʷ
wp1504 c4 L = pw1 c4 L (CCZ024 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ024 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1505 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff413 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ014 ∷ []) ⟫ʷ
wp1505 c4 L = pw2 c4 L (CCZ014 ∷ Toff413 ∷ CCZ013 ∷ []) (Toff413 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1506 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ034 ∷ CCZ023 ∷ []) ⟫ʷ
wp1506 c4 L = pw1 c4 L (CCZ034 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ034 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1507 : Base 4 → WsL → ⟪ (CCZ034 ∷ CCZ023 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ034 ∷ []) ⟫ʷ
wp1507 c4 L = pw1 c4 L (CCZ034 ∷ CCZ023 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1508 : Base 4 → WsL → ⟪ (K3⁻ ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ K3⁻ ∷ []) ⟫ʷ
wp1508 c4 L = pw1 c4 L (K3⁻ ∷ Toff402 ∷ []) (Toff402 ∷ K3⁻ ∷ []) tt tt Eq.refl

wp1509 : Base 4 → WsL → ⟪ (CS23 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS23 ∷ []) ⟫ʷ
wp1509 c4 L = pw1 c4 L (CS23 ∷ Toff402 ∷ []) (Toff402 ∷ CS23 ∷ []) tt tt Eq.refl

wp1510 : Base 4 → WsL → ⟪ (CS12⁻ ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS12⁻ ∷ []) ⟫ʷ
wp1510 c4 L = pw3 c4 L (CS12⁻ ∷ Toff402 ∷ []) (Toff402 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp1511 : Base 4 → WsL → ⟪ (K3 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ K3 ∷ []) ⟫ʷ
wp1511 c4 L = pw1 c4 L (K3 ∷ Toff402 ∷ []) (Toff402 ∷ K3 ∷ []) tt tt Eq.refl

wp1512 : Base 4 → WsL → ⟪ (CCZ012 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ012 ∷ []) ⟫ʷ
wp1512 c4 L = pw3 c4 L (CCZ012 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1513 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ014 ∷ CCZ013 ∷ []) ⟫ʷ
wp1513 c4 L = pw2 c4 L (CCZ014 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ014 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1514 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff423 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ024 ∷ []) ⟫ʷ
wp1514 c4 L = pw1 c4 L (CCZ024 ∷ Toff423 ∷ CCZ023 ∷ []) (Toff423 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1515 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ014 ∷ CCZ013 ∷ []) ⟫ʷ
wp1515 c4 L = pw2 c4 L (CCZ014 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ014 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1516 : Base 4 → WsL → ⟪ (CS24⁻ ∷ CX23 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff302 ∷ CS24⁻ ∷ []) ⟫ʷ
wp1516 c4 L = pw1 c4 L (CS24⁻ ∷ CX23 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp1517 : Base 4 → WsL → ⟪ (CS24 ∷ CX23 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff302 ∷ CS24 ∷ []) ⟫ʷ
wp1517 c4 L = pw1 c4 L (CS24 ∷ CX23 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ CS24 ∷ []) tt tt Eq.refl

wp1518 : Base 4 → WsL → ⟪ (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ
wp1518 c4 L = pw1 c4 L (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ []) tt tt Eq.refl

wp1519 : Base 4 → WsL → ⟪ (K3 ∷ CK03 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ
wp1519 c4 L = pw2 c4 L (K3 ∷ CK03 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ []) tt tt Eq.refl

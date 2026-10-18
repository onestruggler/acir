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

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp1353 : Complete 4 → ⟪ (X0 ∷ CZ14 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wp1353 c4 = pw2 c4 (X0 ∷ CZ14 ∷ CZ14 ∷ []) (X0 ∷ []) tt tt Eq.refl

wp1354 : Complete 4 → ⟪ (Toff302 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) ⟫ʷ
wp1354 c4 = pw1 c4 (Toff302 ∷ Toff423 ∷ []) (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) tt tt Eq.refl

wp1355 : Complete 4 → ⟪ (CS02⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS02⁻ ∷ []) ⟫ʷ
wp1355 c4 = pw1 c4 (CS02⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp1356 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ012 ∷ Toff402 ∷ []) ⟫ʷ
wp1356 c4 = pw3 c4 (CCZ012 ∷ []) (Toff402 ∷ CCZ012 ∷ Toff402 ∷ []) tt tt Eq.refl

wp1357 : Complete 4 → ⟪ (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff302 ∷ []) ⟫ʷ
wp1357 c4 = pw1 c4 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (Toff423 ∷ Toff302 ∷ []) tt tt Eq.refl

wp1358 : Complete 4 → ⟪ (CCZ014 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ []) ⟫ʷ
wp1358 c4 = pw3 c4 (CCZ014 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1359 : Complete 4 → ⟪ (Toff402 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ Toff402 ∷ []) ⟫ʷ
wp1359 c4 = pw3 c4 (Toff402 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff402 ∷ []) tt tt Eq.refl

wp1360 : Complete 4 → ⟪ (CCZ014 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CCZ014 ∷ []) ⟫ʷ
wp1360 c4 = pw2 c4 (CCZ014 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1361 : Complete 4 → ⟪ (Toff413 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ Toff413 ∷ []) ⟫ʷ
wp1361 c4 = pw2 c4 (Toff413 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff413 ∷ []) tt tt Eq.refl

wp1362 : Complete 4 → ⟪ (Toff413 ∷ ι ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ Toff413 ∷ []) ⟫ʷ
wp1362 c4 = pw2 c4 (Toff413 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff413 ∷ []) tt tt Eq.refl

wp1363 : Complete 4 → ⟪ (CCZ024 ∷ K2 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CK02 ∷ S0 ∷ CCZ024 ∷ []) ⟫ʷ
wp1363 c4 = pw3 c4 (CCZ024 ∷ K2 ∷ CK02 ∷ S0 ∷ []) (K2 ∷ CK02 ∷ S0 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1364 : Complete 4 → ⟪ (CCZ014 ∷ Toff103 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ014 ∷ []) ⟫ʷ
wp1364 c4 = pw2 c4 (CCZ014 ∷ Toff103 ∷ CCZ034 ∷ []) (Toff103 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1365 : Complete 4 → ⟪ (CCZ034 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ034 ∷ CCZ023 ∷ []) ⟫ʷ
wp1365 c4 = pw1 c4 (CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ034 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1366 : Complete 4 → ⟪ (Toff103 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ []) ⟫ʷ
wp1366 c4 = pw2 c4 (Toff103 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff103 ∷ []) tt tt Eq.refl

wp1367 : Complete 4 → ⟪ (CCZ023 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ023 ∷ []) ⟫ʷ
wp1367 c4 = pw1 c4 (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1368 : Complete 4 → ⟪ (CCZ234 ∷ CX23 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ []) ⟫ʷ
wp1368 c4 = pw1 c4 (CCZ234 ∷ CX23 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1369 : Complete 4 → ⟪ (CZ24 ∷ CCZ012 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CZ24 ∷ []) ⟫ʷ
wp1369 c4 = pw3 c4 (CZ24 ∷ CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CZ24 ∷ []) tt tt Eq.refl

wp1370 : Complete 4 → ⟪ (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ024 ∷ []) ⟫ʷ
wp1370 c4 = pw3 c4 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1371 : Complete 4 → ⟪ (CZ24 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ CCZ024 ∷ []) ⟫ʷ
wp1371 c4 = pw3 c4 (CZ24 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (CZ24 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1372 : Complete 4 → ⟪ (CCZ234 ∷ CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff302 ∷ CCZ234 ∷ []) ⟫ʷ
wp1372 c4 = pw1 c4 (CCZ234 ∷ CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ []) (CX23 ∷ Toff302 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1373 : Complete 4 → ⟪ (Toff103 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) ⟫ʷ
wp1373 c4 = pw2 c4 (Toff103 ∷ Toff413 ∷ []) (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) tt tt Eq.refl

wp1374 : Complete 4 → ⟪ (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ024 ∷ []) ⟫ʷ
wp1374 c4 = pw1 c4 (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (Toff403 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1375 : Complete 4 → ⟪ (CS03⁻ ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS03⁻ ∷ []) ⟫ʷ
wp1375 c4 = pw2 c4 (CS03⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp1376 : Complete 4 → ⟪ (CS03 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS03 ∷ []) ⟫ʷ
wp1376 c4 = pw2 c4 (CS03 ∷ Toff413 ∷ []) (Toff413 ∷ CS03 ∷ []) tt tt Eq.refl

wp1377 : Complete 4 → ⟪ (Toff403 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff403 ∷ []) ⟫ʷ
wp1377 c4 = pw2 c4 (Toff403 ∷ Toff413 ∷ []) (Toff413 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1378 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ023 ∷ Toff403 ∷ []) ⟫ʷ
wp1378 c4 = pw1 c4 (CCZ023 ∷ []) (Toff403 ∷ CCZ023 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1379 : Complete 4 → ⟪ (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff103 ∷ []) ⟫ʷ
wp1379 c4 = pw2 c4 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (Toff413 ∷ Toff103 ∷ []) tt tt Eq.refl

wp1380 : Complete 4 → ⟪ (CCZ024 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ023 ∷ CCZ024 ∷ []) ⟫ʷ
wp1380 c4 = pw1 c4 (CCZ024 ∷ CX34 ∷ []) (CX34 ∷ CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1381 : Complete 4 → ⟪ (CCZ024 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) ⟫ʷ
wp1381 c4 = pw1 c4 (CCZ024 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1382 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ023 ∷ CX34 ∷ []) ⟫ʷ
wp1382 c4 = pw1 c4 (CCZ023 ∷ []) (CX34 ∷ CCZ023 ∷ CX34 ∷ []) tt tt Eq.refl

wp1383 : Complete 4 → ⟪ (CCZ014 ∷ ι ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp1383 c4 = pw2 c4 (CCZ014 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1384 : Complete 4 → ⟪ (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ []) ⟫ʷ
wp1384 c4 = pw1 c4 (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1385 : Complete 4 → ⟪ (CCZ124 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ124 ∷ CCZ012 ∷ []) ⟫ʷ
wp1385 c4 = pw3 c4 (CCZ124 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ124 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1386 : Complete 4 → ⟪ (CX32 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CX32 ∷ Toff403 ∷ []) ⟫ʷ
wp1386 c4 = pw1 c4 (CX32 ∷ Toff402 ∷ []) (Toff402 ∷ CX32 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1387 : Complete 4 → ⟪ (CCZ134 ∷ Toff403 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ134 ∷ []) ⟫ʷ
wp1387 c4 = pw2 c4 (CCZ134 ∷ Toff403 ∷ CCZ013 ∷ []) (Toff403 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1388 : Complete 4 → ⟪ (CS01 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS01 ∷ []) ⟫ʷ
wp1388 c4 = pw3 c4 (CS01 ∷ Toff402 ∷ []) (Toff402 ∷ CS01 ∷ []) tt tt Eq.refl

wp1389 : Complete 4 → ⟪ (Toff402 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff402 ∷ []) ⟫ʷ
wp1389 c4 = pw1 c4 (Toff402 ∷ Toff403 ∷ []) (Toff403 ∷ Toff402 ∷ []) tt tt Eq.refl

wp1390 : Complete 4 → ⟪ (CX32 ∷ Toff403 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
wp1390 c4 = pw1 c4 (CX32 ∷ Toff403 ∷ Toff403 ∷ []) (CX32 ∷ []) tt tt Eq.refl

wp1391 : Complete 4 → ⟪ (CCZ034 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) ⟫ʷ
wp1391 c4 = pw1 c4 (CCZ034 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) tt tt Eq.refl

wp1392 : Complete 4 → ⟪ (CCZ034 ∷ CZ03 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ []) ⟫ʷ
wp1392 c4 = pw1 c4 (CCZ034 ∷ CZ03 ∷ Toff403 ∷ CCZ034 ∷ []) (Toff403 ∷ []) tt tt Eq.refl

wp1393 : Complete 4 → ⟪ (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ K3 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ
wp1393 c4 = pw1 c4 (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) (Toff403 ∷ K3 ∷ CK03 ∷ S0 ∷ []) tt tt Eq.refl

wp1394 : Complete 4 → ⟪ (Toff401 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ Toff401 ∷ []) ⟫ʷ
wp1394 c4 = pw2 c4 (Toff401 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff401 ∷ []) tt tt Eq.refl

wp1395 : Complete 4 → ⟪ (CCZ014 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CCZ014 ∷ []) ⟫ʷ
wp1395 c4 = pw2 c4 (CCZ014 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1396 : Complete 4 → ⟪ (CCZ034 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ034 ∷ CCZ013 ∷ []) ⟫ʷ
wp1396 c4 = pw2 c4 (CCZ034 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1397 : Complete 4 → ⟪ (CCZ024 ∷ Toff412 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ024 ∷ []) ⟫ʷ
wp1397 c4 = pw3 c4 (CCZ024 ∷ Toff412 ∷ CCZ012 ∷ []) (Toff412 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1398 : Complete 4 → ⟪ (CS01 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS01 ∷ []) ⟫ʷ
wp1398 c4 = pw2 c4 (CS01 ∷ Toff413 ∷ []) (Toff413 ∷ CS01 ∷ []) tt tt Eq.refl

wp1399 : Complete 4 → ⟪ (CCZ034 ∷ CZ03 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
wp1399 c4 = pw1 c4 (CCZ034 ∷ CZ03 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1400 : Complete 4 → ⟪ (CCZ034 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff403 ∷ []) ⟫ʷ
wp1400 c4 = pw1 c4 (CCZ034 ∷ CZ03 ∷ []) (Toff403 ∷ CCZ034 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1401 : Complete 4 → ⟪ (CX01 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CX01 ∷ []) ⟫ʷ
wp1401 c4 = pw2 c4 (CX01 ∷ Toff403 ∷ []) (Toff403 ∷ CX01 ∷ []) tt tt Eq.refl

wp1402 : Complete 4 → ⟪ (CCZ024 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ024 ∷ CCZ023 ∷ []) ⟫ʷ
wp1402 c4 = pw1 c4 (CCZ024 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ024 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1403 : Complete 4 → ⟪ (CX10 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CX10 ∷ Toff413 ∷ []) ⟫ʷ
wp1403 c4 = pw2 c4 (CX10 ∷ Toff403 ∷ []) (Toff403 ∷ CX10 ∷ Toff413 ∷ []) tt tt Eq.refl

wp1404 : Complete 4 → ⟪ (CS23 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS23 ∷ []) ⟫ʷ
wp1404 c4 = pw1 c4 (CS23 ∷ Toff403 ∷ []) (Toff403 ∷ CS23 ∷ []) tt tt Eq.refl

wp1405 : Complete 4 → ⟪ (CX31 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CX31 ∷ []) ⟫ʷ
wp1405 c4 = pw2 c4 (CX31 ∷ Toff403 ∷ []) (Toff403 ∷ CX31 ∷ []) tt tt Eq.refl

wp1406 : Complete 4 → ⟪ (CX10 ∷ Toff413 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wp1406 c4 = pw2 c4 (CX10 ∷ Toff413 ∷ Toff413 ∷ []) (CX10 ∷ []) tt tt Eq.refl

wp1407 : Complete 4 → ⟪ (CX10 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX10 ∷ []) ⟫ʷ
wp1407 c4 = pw2 c4 (CX10 ∷ Toff413 ∷ []) (Toff413 ∷ CX10 ∷ []) tt tt Eq.refl

wp1408 : Complete 4 → ⟪ (CX01 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX01 ∷ Toff403 ∷ []) ⟫ʷ
wp1408 c4 = pw2 c4 (CX01 ∷ Toff413 ∷ []) (Toff413 ∷ CX01 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1409 : Complete 4 → ⟪ (CX30 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX30 ∷ []) ⟫ʷ
wp1409 c4 = pw2 c4 (CX30 ∷ Toff413 ∷ []) (Toff413 ∷ CX30 ∷ []) tt tt Eq.refl

wp1410 : Complete 4 → ⟪ (CX01 ∷ Toff403 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
wp1410 c4 = pw2 c4 (CX01 ∷ Toff403 ∷ Toff403 ∷ []) (CX01 ∷ []) tt tt Eq.refl

wp1411 : Complete 4 → ⟪ (CCZ024 ∷ CCZ034 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ024 ∷ []) ⟫ʷ
wp1411 c4 = pw1 c4 (CCZ024 ∷ CCZ034 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1412 : Complete 4 → ⟪ (CCZ013 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ013 ∷ []) ⟫ʷ
wp1412 c4 = pw2 c4 (CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1413 : Complete 4 → ⟪ (CCZ024 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ024 ∷ CCZ012 ∷ []) ⟫ʷ
wp1413 c4 = pw3 c4 (CCZ024 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1414 : Complete 4 → ⟪ (CCZ034 ∷ Toff413 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ034 ∷ []) ⟫ʷ
wp1414 c4 = pw2 c4 (CCZ034 ∷ Toff413 ∷ CCZ013 ∷ []) (Toff413 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1415 : Complete 4 → ⟪ (CS01 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS01 ∷ []) ⟫ʷ
wp1415 c4 = pw3 c4 (CS01 ∷ Toff412 ∷ []) (Toff412 ∷ CS01 ∷ []) tt tt Eq.refl

wp1416 : Complete 4 → ⟪ (CCZ024 ∷ CZ02 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ024 ∷ []) ⟫ʷ
wp1416 c4 = pw3 c4 (CCZ024 ∷ CZ02 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1417 : Complete 4 → ⟪ (CCZ024 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ024 ∷ Toff402 ∷ []) ⟫ʷ
wp1417 c4 = pw3 c4 (CCZ024 ∷ CZ02 ∷ []) (Toff402 ∷ CCZ024 ∷ Toff402 ∷ []) tt tt Eq.refl

wp1418 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ024 ∷ CZ02 ∷ []) ⟫ʷ
wp1418 c4 = pw3 c4 (CCZ024 ∷ []) (CZ02 ∷ CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl

wp1419 : Complete 4 → ⟪ (CCZ134 ∷ Toff103 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) ⟫ʷ
wp1419 c4 = pw2 c4 (CCZ134 ∷ Toff103 ∷ CCZ034 ∷ []) (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1420 : Complete 4 → ⟪ (CCZ134 ∷ CCZ034 ∷ Toff103 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ
wp1420 c4 = pw2 c4 (CCZ134 ∷ CCZ034 ∷ Toff103 ∷ CCZ034 ∷ []) (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1421 : Complete 4 → ⟪ (CCZ134 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ134 ∷ []) ⟫ʷ
wp1421 c4 = pw2 c4 (CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1422 : Complete 4 → ⟪ (CCZ034 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ034 ∷ []) ⟫ʷ
wp1422 c4 = pw2 c4 (CCZ034 ∷ Toff103 ∷ []) (Toff103 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1423 : Complete 4 → ⟪ (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff301 ∷ []) ⟫ʷ
wp1423 c4 = pw2 c4 (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) (Toff413 ∷ Toff301 ∷ []) tt tt Eq.refl

wp1424 : Complete 4 → ⟪ (CCZ024 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ012 ∷ CCZ024 ∷ []) ⟫ʷ
wp1424 c4 = pw3 c4 (CCZ024 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1425 : Complete 4 → ⟪ (Toff401 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff401 ∷ []) ⟫ʷ
wp1425 c4 = pw2 c4 (Toff401 ∷ Toff413 ∷ []) (Toff413 ∷ Toff401 ∷ []) tt tt Eq.refl

wp1426 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ012 ∷ Toff401 ∷ []) ⟫ʷ
wp1426 c4 = pw3 c4 (CCZ012 ∷ []) (Toff401 ∷ CCZ012 ∷ Toff401 ∷ []) tt tt Eq.refl

wp1427 : Complete 4 → ⟪ (CS34 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS34 ∷ []) ⟫ʷ
wp1427 c4 = pw2 c4 (CS34 ∷ Toff103 ∷ []) (Toff103 ∷ CS34 ∷ []) tt tt Eq.refl

wp1428 : Complete 4 → ⟪ (CS34⁻ ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS34⁻ ∷ []) ⟫ʷ
wp1428 c4 = pw2 c4 (CS34⁻ ∷ Toff103 ∷ []) (Toff103 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1429 : Complete 4 → ⟪ (CS02 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS02 ∷ CS04 ∷ CCZ024 ∷ []) ⟫ʷ
wp1429 c4 = pw3 c4 (CS02 ∷ Toff204 ∷ []) (Toff204 ∷ CS02 ∷ CS04 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1430 : Complete 4 → ⟪ (CS02 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
wp1430 c4 = pw3 c4 (CS02 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) (CS02 ∷ []) tt tt Eq.refl

wp1431 : Complete 4 → ⟪ (CS34 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CS34 ∷ []) ⟫ʷ
wp1431 c4 = pw1 c4 (CS34 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CS34 ∷ []) tt tt Eq.refl

wp1432 : Complete 4 → ⟪ (CS34⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CS34⁻ ∷ []) ⟫ʷ
wp1432 c4 = pw1 c4 (CS34⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1433 : Complete 4 → ⟪ (CZ24 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CZ24 ∷ CCZ014 ∷ []) ⟫ʷ
wp1433 c4 = pw3 c4 (CZ24 ∷ Toff201 ∷ []) (Toff201 ∷ CZ24 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1434 : Complete 4 → ⟪ (CCZ014 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ CCZ014 ∷ []) ⟫ʷ
wp1434 c4 = pw3 c4 (CCZ014 ∷ CZ24 ∷ []) (CZ24 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1435 : Complete 4 → ⟪ (CCZ034 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ014 ∷ CCZ034 ∷ []) ⟫ʷ
wp1435 c4 = pw2 c4 (CCZ034 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1436 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) ⟫ʷ
wp1436 c4 = pw3 c4 (CCZ014 ∷ []) (CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) tt tt Eq.refl

wp1437 : Complete 4 → ⟪ (CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wp1437 c4 = pw3 c4 (CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wp1438 : Complete 4 → ⟪ (CCZ034 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) ⟫ʷ
wp1438 c4 = pw1 c4 (CCZ034 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1439 : Complete 4 → ⟪ (CCZ014 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ014 ∷ CCZ012 ∷ []) ⟫ʷ
wp1439 c4 = pw3 c4 (CCZ014 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1440 : Complete 4 → ⟪ (CCZ034 ∷ Toff423 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ034 ∷ []) ⟫ʷ
wp1440 c4 = pw1 c4 (CCZ034 ∷ Toff423 ∷ CCZ023 ∷ []) (Toff423 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1441 : Complete 4 → ⟪ (CS02 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS02 ∷ []) ⟫ʷ
wp1441 c4 = pw3 c4 (CS02 ∷ Toff412 ∷ []) (Toff412 ∷ CS02 ∷ []) tt tt Eq.refl

wp1442 : Complete 4 → ⟪ (CCZ034 ∷ X0 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ034 ∷ []) ⟫ʷ
wp1442 c4 = pw1 c4 (CCZ034 ∷ X0 ∷ CZ34 ∷ []) (X0 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1443 : Complete 4 → ⟪ (CCZ034 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CZ34 ∷ CCZ034 ∷ []) ⟫ʷ
wp1443 c4 = pw1 c4 (CCZ034 ∷ CZ34 ∷ []) (CZ34 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1444 : Complete 4 → ⟪ (CCZ124 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ124 ∷ []) ⟫ʷ
wp1444 c4 = pw3 c4 (CCZ124 ∷ X0 ∷ []) (X0 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1445 : Complete 4 → ⟪ (K2 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ K2 ∷ []) ⟫ʷ
wp1445 c4 = pw1 c4 (K2 ∷ Toff403 ∷ []) (Toff403 ∷ K2 ∷ []) tt tt Eq.refl

wp1446 : Complete 4 → ⟪ (CS02 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS02 ∷ []) ⟫ʷ
wp1446 c4 = pw1 c4 (CS02 ∷ Toff403 ∷ []) (Toff403 ∷ CS02 ∷ []) tt tt Eq.refl

wp1447 : Complete 4 → ⟪ (CS02⁻ ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS02⁻ ∷ []) ⟫ʷ
wp1447 c4 = pw1 c4 (CS02⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp1448 : Complete 4 → ⟪ (CS01 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS01 ∷ []) ⟫ʷ
wp1448 c4 = pw2 c4 (CS01 ∷ Toff403 ∷ []) (Toff403 ∷ CS01 ∷ []) tt tt Eq.refl

wp1449 : Complete 4 → ⟪ (K2⁻ ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ K2⁻ ∷ []) ⟫ʷ
wp1449 c4 = pw1 c4 (K2⁻ ∷ Toff403 ∷ []) (Toff403 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp1450 : Complete 4 → ⟪ (CCZ124 ∷ CX12 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ []) ⟫ʷ
wp1450 c4 = pw3 c4 (CCZ124 ∷ CX12 ∷ Toff201 ∷ []) (CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1451 : Complete 4 → ⟪ (CZ14 ∷ CCZ013 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CZ14 ∷ []) ⟫ʷ
wp1451 c4 = pw2 c4 (CZ14 ∷ CCZ013 ∷ Toff403 ∷ []) (Toff403 ∷ CZ14 ∷ []) tt tt Eq.refl

wp1452 : Complete 4 → ⟪ (CCZ014 ∷ CCZ013 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ014 ∷ []) ⟫ʷ
wp1452 c4 = pw2 c4 (CCZ014 ∷ CCZ013 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1453 : Complete 4 → ⟪ (CZ14 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ CCZ014 ∷ []) ⟫ʷ
wp1453 c4 = pw2 c4 (CZ14 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) (CZ14 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1454 : Complete 4 → ⟪ (CCZ124 ∷ CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff201 ∷ CCZ124 ∷ []) ⟫ʷ
wp1454 c4 = pw3 c4 (CCZ124 ∷ CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ []) (CX12 ∷ Toff201 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1455 : Complete 4 → ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ
wp1455 c4 = pw2 c4 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1456 : Complete 4 → ⟪ (CCZ014 ∷ Toff401 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ014 ∷ []) ⟫ʷ
wp1456 c4 = pw2 c4 (CCZ014 ∷ Toff401 ∷ CZ01 ∷ []) (Toff401 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1457 : Complete 4 → ⟪ (CCZ014 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CZ01 ∷ CCZ014 ∷ []) ⟫ʷ
wp1457 c4 = pw2 c4 (CCZ014 ∷ Toff401 ∷ []) (Toff401 ∷ CZ01 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1458 : Complete 4 → ⟪ (CCZ024 ∷ Toff402 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ024 ∷ []) ⟫ʷ
wp1458 c4 = pw3 c4 (CCZ024 ∷ Toff402 ∷ CZ02 ∷ []) (Toff402 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1459 : Complete 4 → ⟪ (CCZ024 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CZ02 ∷ CCZ024 ∷ []) ⟫ʷ
wp1459 c4 = pw3 c4 (CCZ024 ∷ Toff402 ∷ []) (Toff402 ∷ CZ02 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1460 : Complete 4 → ⟪ (Toff403 ∷ Toff203 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff203 ∷ []) ⟫ʷ
wp1460 c4 = pw1 c4 (Toff403 ∷ Toff203 ∷ Toff423 ∷ []) (Toff423 ∷ Toff203 ∷ []) tt tt Eq.refl

wp1461 : Complete 4 → ⟪ (CCZ014 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ013 ∷ CCZ014 ∷ []) ⟫ʷ
wp1461 c4 = pw2 c4 (CCZ014 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ013 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1462 : Complete 4 → ⟪ (Toff403 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff403 ∷ []) ⟫ʷ
wp1462 c4 = pw1 c4 (Toff403 ∷ Toff423 ∷ []) (Toff423 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1463 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ013 ∷ Toff403 ∷ []) ⟫ʷ
wp1463 c4 = pw2 c4 (CCZ013 ∷ []) (Toff403 ∷ CCZ013 ∷ Toff403 ∷ []) tt tt Eq.refl

wp1464 : Complete 4 → ⟪ (CCZ014 ∷ CCZ013 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ014 ∷ []) ⟫ʷ
wp1464 c4 = pw2 c4 (CCZ014 ∷ CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1465 : Complete 4 → ⟪ (Toff201 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
wp1465 c4 = pw3 c4 (Toff201 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff201 ∷ []) tt tt Eq.refl

wp1466 : Complete 4 → ⟪ (CCZ234 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) ⟫ʷ
wp1466 c4 = pw1 c4 (CCZ234 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1467 : Complete 4 → ⟪ (CCZ024 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ
wp1467 c4 = pw1 c4 (CCZ024 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1468 : Complete 4 → ⟪ (CCZ034 ∷ CCZ013 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ034 ∷ []) ⟫ʷ
wp1468 c4 = pw2 c4 (CCZ034 ∷ CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1469 : Complete 4 → ⟪ (Toff203 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
wp1469 c4 = pw1 c4 (Toff203 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff203 ∷ []) tt tt Eq.refl

wp1470 : Complete 4 → ⟪ (CS04⁻ ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS04⁻ ∷ CS02⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp1470 c4 = pw3 c4 (CS04⁻ ∷ Toff402 ∷ []) (Toff402 ∷ CS04⁻ ∷ CS02⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1471 : Complete 4 → ⟪ (CS02⁻ ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS02⁻ ∷ []) ⟫ʷ
wp1471 c4 = pw3 c4 (CS02⁻ ∷ Toff402 ∷ []) (Toff402 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp1472 : Complete 4 → ⟪ (CS04⁻ ∷ CS02⁻ ∷ CCZ024 ∷ CS02⁻ ∷ CZ02 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ []) ⟫ʷ
wp1472 c4 = pw3 c4 (CS04⁻ ∷ CS02⁻ ∷ CCZ024 ∷ CS02⁻ ∷ CZ02 ∷ CCZ024 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl

wp1473 : Complete 4 → ⟪ (S4 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ S4 ∷ CS02 ∷ CCZ024 ∷ []) ⟫ʷ
wp1473 c4 = pw3 c4 (S4 ∷ Toff402 ∷ []) (Toff402 ∷ S4 ∷ CS02 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1474 : Complete 4 → ⟪ (CS02 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS02 ∷ []) ⟫ʷ
wp1474 c4 = pw3 c4 (CS02 ∷ Toff402 ∷ []) (Toff402 ∷ CS02 ∷ []) tt tt Eq.refl

wp1475 : Complete 4 → ⟪ (S4 ∷ CS02 ∷ CCZ024 ∷ CS02 ∷ CZ02 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ []) ⟫ʷ
wp1475 c4 = pw3 c4 (S4 ∷ CS02 ∷ CCZ024 ∷ CS02 ∷ CZ02 ∷ CCZ024 ∷ []) (S4 ∷ []) tt tt Eq.refl

wp1476 : Complete 4 → ⟪ (Toff103 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ Toff103 ∷ []) ⟫ʷ
wp1476 c4 = pw2 c4 (Toff103 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ Toff103 ∷ []) tt tt Eq.refl

wp1477 : Complete 4 → ⟪ (CS12 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS12 ∷ []) ⟫ʷ
wp1477 c4 = pw3 c4 (CS12 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS12 ∷ []) tt tt Eq.refl

wp1478 : Complete 4 → ⟪ (CS12⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS12⁻ ∷ []) ⟫ʷ
wp1478 c4 = pw3 c4 (CS12⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp1479 : Complete 4 → ⟪ (CCZ024 ∷ CCZ023 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ024 ∷ []) ⟫ʷ
wp1479 c4 = pw1 c4 (CCZ024 ∷ CCZ023 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1480 : Complete 4 → ⟪ (CCZ134 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ134 ∷ CCZ013 ∷ []) ⟫ʷ
wp1480 c4 = pw2 c4 (CCZ134 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ134 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1481 : Complete 4 → ⟪ (CS13⁻ ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS13⁻ ∷ []) ⟫ʷ
wp1481 c4 = pw2 c4 (CS13⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp1482 : Complete 4 → ⟪ (CS13 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS13 ∷ []) ⟫ʷ
wp1482 c4 = pw2 c4 (CS13 ∷ Toff403 ∷ []) (Toff403 ∷ CS13 ∷ []) tt tt Eq.refl

wp1483 : Complete 4 → ⟪ (CCZ013 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ013 ∷ []) ⟫ʷ
wp1483 c4 = pw2 c4 (CCZ013 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1484 : Complete 4 → ⟪ (Toff301 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff401 ∷ Toff301 ∷ []) ⟫ʷ
wp1484 c4 = pw2 c4 (Toff301 ∷ Toff413 ∷ []) (Toff413 ∷ Toff401 ∷ Toff301 ∷ []) tt tt Eq.refl

wp1485 : Complete 4 → ⟪ (CCZ024 ∷ Toff401 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ024 ∷ []) ⟫ʷ
wp1485 c4 = pw3 c4 (CCZ024 ∷ Toff401 ∷ CCZ012 ∷ []) (Toff401 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1486 : Complete 4 → ⟪ (CX31 ∷ Toff103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX31 ∷ Toff103 ∷ []) ⟫ʷ
wp1486 c4 = pw2 c4 (CX31 ∷ Toff103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX31 ∷ Toff103 ∷ []) tt tt Eq.refl

wp1487 : Complete 4 → ⟪ (CX31 ∷ CCZ034 ∷ Toff103 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Toff103 ∷ []) ⟫ʷ
wp1487 c4 = pw2 c4 (CX31 ∷ CCZ034 ∷ Toff103 ∷ CCZ034 ∷ []) (CX31 ∷ Toff103 ∷ []) tt tt Eq.refl

wp1488 : Complete 4 → ⟪ (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ
wp1488 c4 = pw3 c4 (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CK02 ∷ []) tt tt Eq.refl

wp1489 : Complete 4 → ⟪ (CS02⁻ ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS02⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp1489 c4 = pw3 c4 (CS02⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS02⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1490 : Complete 4 → ⟪ (CS02⁻ ∷ CS04⁻ ∷ CCZ024 ∷ CS04⁻ ∷ CZ04 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wp1490 c4 = pw3 c4 (CS02⁻ ∷ CS04⁻ ∷ CCZ024 ∷ CS04⁻ ∷ CZ04 ∷ CCZ024 ∷ []) (CS02⁻ ∷ []) tt tt Eq.refl

wp1491 : Complete 4 → ⟪ (CS34⁻ ∷ K2 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CK02 ∷ S0 ∷ CS34⁻ ∷ []) ⟫ʷ
wp1491 c4 = pw1 c4 (CS34⁻ ∷ K2 ∷ CK02 ∷ S0 ∷ []) (K2 ∷ CK02 ∷ S0 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1492 : Complete 4 → ⟪ (CS34 ∷ K2 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CK02 ∷ S0 ∷ CS34 ∷ []) ⟫ʷ
wp1492 c4 = pw1 c4 (CS34 ∷ K2 ∷ CK02 ∷ S0 ∷ []) (K2 ∷ CK02 ∷ S0 ∷ CS34 ∷ []) tt tt Eq.refl

wp1493 : Complete 4 → ⟪ (CCZ024 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CCZ024 ∷ []) ⟫ʷ
wp1493 c4 = pw1 c4 (CCZ024 ∷ S0 ∷ []) (S0 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1494 : Complete 4 → ⟪ (CS04⁻ ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp1494 c4 = pw2 c4 (CS04⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1495 : Complete 4 → ⟪ (CS01⁻ ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS01⁻ ∷ []) ⟫ʷ
wp1495 c4 = pw2 c4 (CS01⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp1496 : Complete 4 → ⟪ (CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ CS01⁻ ∷ CZ01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ []) ⟫ʷ
wp1496 c4 = pw2 c4 (CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ CS01⁻ ∷ CZ01 ∷ CCZ014 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl

wp1497 : Complete 4 → ⟪ (S4 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ S4 ∷ CS01 ∷ CCZ014 ∷ []) ⟫ʷ
wp1497 c4 = pw2 c4 (S4 ∷ Toff401 ∷ []) (Toff401 ∷ S4 ∷ CS01 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1498 : Complete 4 → ⟪ (CS01 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS01 ∷ []) ⟫ʷ
wp1498 c4 = pw2 c4 (CS01 ∷ Toff401 ∷ []) (Toff401 ∷ CS01 ∷ []) tt tt Eq.refl

wp1499 : Complete 4 → ⟪ (S4 ∷ CS01 ∷ CCZ014 ∷ CS01 ∷ CZ01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ []) ⟫ʷ
wp1499 c4 = pw2 c4 (S4 ∷ CS01 ∷ CCZ014 ∷ CS01 ∷ CZ01 ∷ CCZ014 ∷ []) (S4 ∷ []) tt tt Eq.refl

wp1500 : Complete 4 → ⟪ (Toff302 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ Toff302 ∷ []) ⟫ʷ
wp1500 c4 = pw1 c4 (Toff302 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ Toff302 ∷ []) tt tt Eq.refl

wp1501 : Complete 4 → ⟪ (CS13 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS13 ∷ []) ⟫ʷ
wp1501 c4 = pw2 c4 (CS13 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS13 ∷ []) tt tt Eq.refl

wp1502 : Complete 4 → ⟪ (CS13⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS13⁻ ∷ []) ⟫ʷ
wp1502 c4 = pw2 c4 (CS13⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp1503 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ []) ⟫ʷ
wp1503 c4 = pw2 c4 (CCZ014 ∷ []) (CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ []) tt tt Eq.refl

wp1504 : Complete 4 → ⟪ (CCZ024 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ024 ∷ CCZ023 ∷ []) ⟫ʷ
wp1504 c4 = pw1 c4 (CCZ024 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ024 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1505 : Complete 4 → ⟪ (CCZ014 ∷ Toff413 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ014 ∷ []) ⟫ʷ
wp1505 c4 = pw2 c4 (CCZ014 ∷ Toff413 ∷ CCZ013 ∷ []) (Toff413 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1506 : Complete 4 → ⟪ (CCZ034 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ034 ∷ CCZ023 ∷ []) ⟫ʷ
wp1506 c4 = pw1 c4 (CCZ034 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ034 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1507 : Complete 4 → ⟪ (CCZ034 ∷ CCZ023 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ034 ∷ []) ⟫ʷ
wp1507 c4 = pw1 c4 (CCZ034 ∷ CCZ023 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1508 : Complete 4 → ⟪ (K3⁻ ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ K3⁻ ∷ []) ⟫ʷ
wp1508 c4 = pw1 c4 (K3⁻ ∷ Toff402 ∷ []) (Toff402 ∷ K3⁻ ∷ []) tt tt Eq.refl

wp1509 : Complete 4 → ⟪ (CS23 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS23 ∷ []) ⟫ʷ
wp1509 c4 = pw1 c4 (CS23 ∷ Toff402 ∷ []) (Toff402 ∷ CS23 ∷ []) tt tt Eq.refl

wp1510 : Complete 4 → ⟪ (CS12⁻ ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS12⁻ ∷ []) ⟫ʷ
wp1510 c4 = pw3 c4 (CS12⁻ ∷ Toff402 ∷ []) (Toff402 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp1511 : Complete 4 → ⟪ (K3 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ K3 ∷ []) ⟫ʷ
wp1511 c4 = pw1 c4 (K3 ∷ Toff402 ∷ []) (Toff402 ∷ K3 ∷ []) tt tt Eq.refl

wp1512 : Complete 4 → ⟪ (CCZ012 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ012 ∷ []) ⟫ʷ
wp1512 c4 = pw3 c4 (CCZ012 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1513 : Complete 4 → ⟪ (CCZ014 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ014 ∷ CCZ013 ∷ []) ⟫ʷ
wp1513 c4 = pw2 c4 (CCZ014 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ014 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1514 : Complete 4 → ⟪ (CCZ024 ∷ Toff423 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ024 ∷ []) ⟫ʷ
wp1514 c4 = pw1 c4 (CCZ024 ∷ Toff423 ∷ CCZ023 ∷ []) (Toff423 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1515 : Complete 4 → ⟪ (CCZ014 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ014 ∷ CCZ013 ∷ []) ⟫ʷ
wp1515 c4 = pw2 c4 (CCZ014 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ014 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1516 : Complete 4 → ⟪ (CS24⁻ ∷ CX23 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff302 ∷ CS24⁻ ∷ []) ⟫ʷ
wp1516 c4 = pw1 c4 (CS24⁻ ∷ CX23 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp1517 : Complete 4 → ⟪ (CS24 ∷ CX23 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff302 ∷ CS24 ∷ []) ⟫ʷ
wp1517 c4 = pw1 c4 (CS24 ∷ CX23 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ CS24 ∷ []) tt tt Eq.refl

wp1518 : Complete 4 → ⟪ (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ
wp1518 c4 = pw1 c4 (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ []) tt tt Eq.refl

wp1519 : Complete 4 → ⟪ (K3 ∷ CK03 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ
wp1519 c4 = pw2 c4 (K3 ∷ CK03 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ []) tt tt Eq.refl

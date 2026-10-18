------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL07 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl1312 : Complete 4 → ⟪ (K1⁻ ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ K1⁻ ∷ []) ⟫ʷ
wl1312 c4 = lw4 c4 (K1⁻ ∷ Toff302 ∷ []) (Toff302 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl1313 : Complete 4 → ⟪ (K1 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ []) ⟫ʷ
wl1313 c4 = lw0 c4 (K1 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ K1⁻ ∷ []) (Toff124 ∷ []) tt tt Eq.refl

wl1314 : Complete 4 → ⟪ (CCZ134 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ CCZ234 ∷ CCZ134 ∷ []) ⟫ʷ
wl1314 c4 = lw0 c4 (CCZ134 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ234 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1315 : Complete 4 → ⟪ (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
wl1315 c4 = lw0 c4 (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ []) tt tt Eq.refl

wl1316 : Complete 4 → ⟪ (CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ []) ⟫ʷ
wl1316 c4 = lw0 c4 (CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Toff234 ∷ []) tt tt Eq.refl

wl1317 : Complete 4 → ⟪ (CCZ013 ∷ CX20 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ013 ∷ []) ⟫ʷ
wl1317 c4 = lw4 c4 (CCZ013 ∷ CX20 ∷ CCZ123 ∷ []) (CX20 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1318 : Complete 4 → ⟪ (CX20 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
wl1318 c4 = lw4 c4 (CX20 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX20 ∷ []) tt tt Eq.refl

wl1319 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) ⟫ʷ
wl1319 c4 = lw0 c4 (CCZ123 ∷ []) (CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) tt tt Eq.refl

wl1320 : Complete 4 → ⟪ (CCZ123 ∷ CX03 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ123 ∷ []) ⟫ʷ
wl1320 c4 = lw4 c4 (CCZ123 ∷ CX03 ∷ CCZ012 ∷ []) (CX03 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1321 : Complete 4 → ⟪ (CCZ123 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl1321 c4 = lw4 c4 (CCZ123 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1322 : Complete 4 → ⟪ (CX03 ∷ CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
wl1322 c4 = lw4 c4 (CX03 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX03 ∷ []) tt tt Eq.refl

wl1323 : Complete 4 → ⟪ (CCZ123 ∷ Toff234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ123 ∷ []) ⟫ʷ
wl1323 c4 = lw0 c4 (CCZ123 ∷ Toff234 ∷ CCZ134 ∷ []) (Toff234 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1324 : Complete 4 → ⟪ (CCZ123 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ123 ∷ []) ⟫ʷ
wl1324 c4 = lw4 c4 (CCZ123 ∷ CX30 ∷ []) (CX30 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1325 : Complete 4 → ⟪ (CCZ123 ∷ CX02 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ CCZ123 ∷ []) ⟫ʷ
wl1325 c4 = lw4 c4 (CCZ123 ∷ CX02 ∷ CCZ013 ∷ []) (CX02 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1326 : Complete 4 → ⟪ (CX02 ∷ CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
wl1326 c4 = lw4 c4 (CX02 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX02 ∷ []) tt tt Eq.refl

wl1327 : Complete 4 → ⟪ (CCZ123 ∷ Toff324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ123 ∷ []) ⟫ʷ
wl1327 c4 = lw0 c4 (CCZ123 ∷ Toff324 ∷ CCZ124 ∷ []) (Toff324 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1328 : Complete 4 → ⟪ (CCZ123 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ123 ∷ CCZ013 ∷ []) ⟫ʷ
wl1328 c4 = lw4 c4 (CCZ123 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ123 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1329 : Complete 4 → ⟪ (CS03 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS03 ∷ []) ⟫ʷ
wl1329 c4 = lw4 c4 (CS03 ∷ Toff201 ∷ []) (Toff201 ∷ CS03 ∷ []) tt tt Eq.refl

wl1330 : Complete 4 → ⟪ (CCZ123 ∷ CCZ012 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ123 ∷ []) ⟫ʷ
wl1330 c4 = lw4 c4 (CCZ123 ∷ CCZ012 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1331 : Complete 4 → ⟪ (K2⁻ ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ K2⁻ ∷ []) ⟫ʷ
wl1331 c4 = lw4 c4 (K2⁻ ∷ Toff301 ∷ []) (Toff301 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl1332 : Complete 4 → ⟪ (CS14 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CS14 ∷ []) ⟫ʷ
wl1332 c4 = lw0 c4 (CS14 ∷ Toff234 ∷ []) (Toff234 ∷ CS14 ∷ []) tt tt Eq.refl

wl1333 : Complete 4 → ⟪ (CCZ123 ∷ CCZ134 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ123 ∷ []) ⟫ʷ
wl1333 c4 = lw0 c4 (CCZ123 ∷ CCZ134 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1334 : Complete 4 → ⟪ (CCZ123 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ123 ∷ Toff234 ∷ []) ⟫ʷ
wl1334 c4 = lw0 c4 (CCZ123 ∷ CCZ134 ∷ []) (Toff234 ∷ CCZ123 ∷ Toff234 ∷ []) tt tt Eq.refl

wl1335 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) ⟫ʷ
wl1335 c4 = lw0 c4 (CCZ123 ∷ []) (CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1336 : Complete 4 → ⟪ (CCZ124 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ124 ∷ CCZ134 ∷ []) ⟫ʷ
wl1336 c4 = lw0 c4 (CCZ124 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1337 : Complete 4 → ⟪ (CX01 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX01 ∷ Toff203 ∷ []) ⟫ʷ
wl1337 c4 = lw4 c4 (CX01 ∷ Toff213 ∷ []) (Toff213 ∷ CX01 ∷ Toff203 ∷ []) tt tt Eq.refl

wl1338 : Complete 4 → ⟪ (Toff203 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff203 ∷ []) ⟫ʷ
wl1338 c4 = lw4 c4 (Toff203 ∷ Toff213 ∷ []) (Toff213 ∷ Toff203 ∷ []) tt tt Eq.refl

wl1339 : Complete 4 → ⟪ (CX01 ∷ Toff203 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
wl1339 c4 = lw4 c4 (CX01 ∷ Toff203 ∷ Toff203 ∷ []) (CX01 ∷ []) tt tt Eq.refl

wl1340 : Complete 4 → ⟪ (Sw01 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Sw01 ∷ []) ⟫ʷ
wl1340 c4 = lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl

wl1341 : Complete 4 → ⟪ (CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wl1341 c4 = lw0 c4 (CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wl1342 : Complete 4 → ⟪ (CCZ234 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ134 ∷ CCZ234 ∷ []) ⟫ʷ
wl1342 c4 = lw0 c4 (CCZ234 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1343 : Complete 4 → ⟪ (CCZ023 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ023 ∷ []) ⟫ʷ
wl1343 c4 = lw4 c4 (CCZ023 ∷ CX31 ∷ []) (CX31 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1344 : Complete 4 → ⟪ (CCZ134 ∷ CCZ234 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ234 ∷ []) ⟫ʷ
wl1344 c4 = lw0 c4 (CCZ134 ∷ CCZ234 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1345 : Complete 4 → ⟪ (CCZ023 ∷ Toff301 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ023 ∷ []) ⟫ʷ
wl1345 c4 = lw4 c4 (CCZ023 ∷ Toff301 ∷ CCZ012 ∷ []) (Toff301 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1346 : Complete 4 → ⟪ (K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ []) ⟫ʷ
wl1346 c4 = lw4 c4 (K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ []) (Toff301 ∷ []) tt tt Eq.refl

wl1347 : Complete 4 → ⟪ (Toff301 ∷ CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ []) ⟫ʷ
wl1347 c4 = lw4 c4 (Toff301 ∷ CCZ012 ∷ CCZ012 ∷ []) (Toff301 ∷ []) tt tt Eq.refl

wl1348 : Complete 4 → ⟪ (CX01 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CX01 ∷ []) ⟫ʷ
wl1348 c4 = lw4 c4 (CX01 ∷ Toff203 ∷ []) (Toff203 ∷ CX01 ∷ []) tt tt Eq.refl

wl1349 : Complete 4 → ⟪ (CX10 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CX10 ∷ Toff213 ∷ []) ⟫ʷ
wl1349 c4 = lw4 c4 (CX10 ∷ Toff203 ∷ []) (Toff203 ∷ CX10 ∷ Toff213 ∷ []) tt tt Eq.refl

wl1350 : Complete 4 → ⟪ (CCZ124 ∷ Toff213 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ124 ∷ []) ⟫ʷ
wl1350 c4 = lw0 c4 (CCZ124 ∷ Toff213 ∷ CCZ134 ∷ []) (Toff213 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1351 : Complete 4 → ⟪ (CX31 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CX31 ∷ []) ⟫ʷ
wl1351 c4 = lw4 c4 (CX31 ∷ Toff203 ∷ []) (Toff203 ∷ CX31 ∷ []) tt tt Eq.refl

wl1352 : Complete 4 → ⟪ (CX10 ∷ Toff213 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wl1352 c4 = lw4 c4 (CX10 ∷ Toff213 ∷ Toff213 ∷ []) (CX10 ∷ []) tt tt Eq.refl

wl1353 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) ⟫ʷ
wl1353 c4 = lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) tt tt Eq.refl

wl1354 : Complete 4 → ⟪ (CCZ123 ∷ CCZ013 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ123 ∷ []) ⟫ʷ
wl1354 c4 = lw4 c4 (CCZ123 ∷ CCZ013 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1355 : Complete 4 → ⟪ (CCZ123 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ123 ∷ Toff324 ∷ []) ⟫ʷ
wl1355 c4 = lw0 c4 (CCZ123 ∷ CCZ124 ∷ []) (Toff324 ∷ CCZ123 ∷ Toff324 ∷ []) tt tt Eq.refl

wl1356 : Complete 4 → ⟪ (CCZ134 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ134 ∷ CCZ124 ∷ []) ⟫ʷ
wl1356 c4 = lw0 c4 (CCZ134 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ134 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1357 : Complete 4 → ⟪ (CX01 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX01 ∷ Toff302 ∷ []) ⟫ʷ
wl1357 c4 = lw4 c4 (CX01 ∷ Toff312 ∷ []) (Toff312 ∷ CX01 ∷ Toff302 ∷ []) tt tt Eq.refl

wl1358 : Complete 4 → ⟪ (Toff302 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff302 ∷ []) ⟫ʷ
wl1358 c4 = lw4 c4 (Toff302 ∷ Toff312 ∷ []) (Toff312 ∷ Toff302 ∷ []) tt tt Eq.refl

wl1359 : Complete 4 → ⟪ (CX01 ∷ Toff302 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
wl1359 c4 = lw4 c4 (CX01 ∷ Toff302 ∷ Toff302 ∷ []) (CX01 ∷ []) tt tt Eq.refl

wl1360 : Complete 4 → ⟪ (CCZ234 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ124 ∷ CCZ234 ∷ []) ⟫ʷ
wl1360 c4 = lw0 c4 (CCZ234 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ124 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1361 : Complete 4 → ⟪ (CCZ124 ∷ CCZ234 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ234 ∷ []) ⟫ʷ
wl1361 c4 = lw0 c4 (CCZ124 ∷ CCZ234 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1362 : Complete 4 → ⟪ (CCZ023 ∷ Toff201 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ023 ∷ []) ⟫ʷ
wl1362 c4 = lw4 c4 (CCZ023 ∷ Toff201 ∷ CCZ013 ∷ []) (Toff201 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1363 : Complete 4 → ⟪ (K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
wl1363 c4 = lw4 c4 (K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ []) (Toff201 ∷ []) tt tt Eq.refl

wl1364 : Complete 4 → ⟪ (K2⁻ ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ K2⁻ ∷ []) ⟫ʷ
wl1364 c4 = lw0 c4 (K2⁻ ∷ Toff314 ∷ []) (Toff314 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl1365 : Complete 4 → ⟪ (K2 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ K2 ∷ []) ⟫ʷ
wl1365 c4 = lw0 c4 (K2 ∷ Toff314 ∷ []) (Toff314 ∷ K2 ∷ []) tt tt Eq.refl

wl1366 : Complete 4 → ⟪ (Toff201 ∷ CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
wl1366 c4 = lw4 c4 (Toff201 ∷ CCZ013 ∷ CCZ013 ∷ []) (Toff201 ∷ []) tt tt Eq.refl

wl1367 : Complete 4 → ⟪ (CX10 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CX10 ∷ Toff312 ∷ []) ⟫ʷ
wl1367 c4 = lw4 c4 (CX10 ∷ Toff302 ∷ []) (Toff302 ∷ CX10 ∷ Toff312 ∷ []) tt tt Eq.refl

wl1368 : Complete 4 → ⟪ (CCZ134 ∷ Toff312 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ134 ∷ []) ⟫ʷ
wl1368 c4 = lw0 c4 (CCZ134 ∷ Toff312 ∷ CCZ124 ∷ []) (Toff312 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1369 : Complete 4 → ⟪ (CX10 ∷ Toff312 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wl1369 c4 = lw4 c4 (CX10 ∷ Toff312 ∷ Toff312 ∷ []) (CX10 ∷ []) tt tt Eq.refl

wl1370 : Complete 4 → ⟪ (CCZ013 ∷ Toff301 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ []) ⟫ʷ
wl1370 c4 = lw4 c4 (CCZ013 ∷ Toff301 ∷ CZ01 ∷ []) (Toff301 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1371 : Complete 4 → ⟪ (CS24⁻ ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS24⁻ ∷ []) ⟫ʷ
wl1371 c4 = lw0 c4 (CS24⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl1372 : Complete 4 → ⟪ (Toff234 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) ⟫ʷ
wl1372 c4 = lw0 c4 (Toff234 ∷ Toff234 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) tt tt Eq.refl

wl1373 : Complete 4 → ⟪ (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1373 c4 = lw0 c4 (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) [] tt tt Eq.refl

wl1374 : Complete 4 → ⟪ (K2 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ []) ⟫ʷ
wl1374 c4 = lw0 c4 (K2 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl

wl1375 : Complete 4 → ⟪ (K2⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ K2⁻ ∷ []) ⟫ʷ
wl1375 c4 = lw4 c4 (K2⁻ ∷ Toff013 ∷ []) (Toff013 ∷ K2⁻ ∷ []) tt tt Eq.refl

wl1376 : Complete 4 → ⟪ (K2 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ []) ⟫ʷ
wl1376 c4 = lw0 c4 (K2 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl

wl1377 : Complete 4 → ⟪ (CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ []) ⟫ʷ
wl1377 c4 = lw0 c4 (CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ []) (CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1378 : Complete 4 → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1378 c4 = lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) [] tt tt Eq.refl

wl1379 : Complete 4 → ⟪ (CCZ134 ∷ Toff134 ∷ CZ12 ∷ Toff134 ∷ CCZ134 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
wl1379 c4 = lw0 c4 (CCZ134 ∷ Toff134 ∷ CZ12 ∷ Toff134 ∷ CCZ134 ∷ CZ12 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl

wl1380 : Complete 4 → ⟪ (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ []) ⟫ʷ
wl1380 c4 = lw4 c4 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (Toff301 ∷ []) tt tt Eq.refl

wl1381 : Complete 4 → ⟪ (Toff201 ∷ Toff301 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff201 ∷ []) ⟫ʷ
wl1381 c4 = lw4 c4 (Toff201 ∷ Toff301 ∷ Toff312 ∷ []) (Toff312 ∷ Toff201 ∷ []) tt tt Eq.refl

wl1382 : Complete 4 → ⟪ (CCZ234 ∷ CCZ124 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ234 ∷ []) ⟫ʷ
wl1382 c4 = lw0 c4 (CCZ234 ∷ CCZ124 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1383 : Complete 4 → ⟪ (CCZ234 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ234 ∷ Toff312 ∷ []) ⟫ʷ
wl1383 c4 = lw0 c4 (CCZ234 ∷ CCZ124 ∷ []) (Toff312 ∷ CCZ234 ∷ Toff312 ∷ []) tt tt Eq.refl

wl1384 : Complete 4 → ⟪ (CS12 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS12 ∷ []) ⟫ʷ
wl1384 c4 = lw4 c4 (CS12 ∷ Toff301 ∷ []) (Toff301 ∷ CS12 ∷ []) tt tt Eq.refl

wl1385 : Complete 4 → ⟪ (CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
wl1385 c4 = lw0 c4 (CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl

wl1386 : Complete 4 → ⟪ (Toff201 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff201 ∷ []) ⟫ʷ
wl1386 c4 = lw4 c4 (Toff201 ∷ Toff301 ∷ []) (Toff301 ∷ Toff201 ∷ []) tt tt Eq.refl

wl1387 : Complete 4 → ⟪ (K2 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
wl1387 c4 = lw4 c4 (K2 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K2⁻ ∷ []) (Toff201 ∷ []) tt tt Eq.refl

wl1388 : Complete 4 → ⟪ (CCZ234 ∷ CX13 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ234 ∷ []) ⟫ʷ
wl1388 c4 = lw0 c4 (CCZ234 ∷ CX13 ∷ CCZ124 ∷ []) (CX13 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1389 : Complete 4 → ⟪ (CX13 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
wl1389 c4 = lw0 c4 (CX13 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX13 ∷ []) tt tt Eq.refl

wl1390 : Complete 4 → ⟪ (CX31 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CX31 ∷ Toff203 ∷ []) ⟫ʷ
wl1390 c4 = lw4 c4 (CX31 ∷ Toff201 ∷ []) (Toff201 ∷ CX31 ∷ Toff203 ∷ []) tt tt Eq.refl

wl1391 : Complete 4 → ⟪ (Toff201 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff201 ∷ []) ⟫ʷ
wl1391 c4 = lw4 c4 (Toff201 ∷ Toff203 ∷ []) (Toff203 ∷ Toff201 ∷ []) tt tt Eq.refl

wl1392 : Complete 4 → ⟪ (CX31 ∷ Toff203 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
wl1392 c4 = lw4 c4 (CX31 ∷ Toff203 ∷ Toff203 ∷ []) (CX31 ∷ []) tt tt Eq.refl

wl1393 : Complete 4 → ⟪ (CCZ023 ∷ CX13 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ023 ∷ []) ⟫ʷ
wl1393 c4 = lw4 c4 (CCZ023 ∷ CX13 ∷ CCZ012 ∷ []) (CX13 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1394 : Complete 4 → ⟪ (CX13 ∷ CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
wl1394 c4 = lw4 c4 (CX13 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX13 ∷ []) tt tt Eq.refl

wl1395 : Complete 4 → ⟪ (CCZ023 ∷ CCZ012 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ023 ∷ []) ⟫ʷ
wl1395 c4 = lw4 c4 (CCZ023 ∷ CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1396 : Complete 4 → ⟪ (CCZ234 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ234 ∷ CCZ124 ∷ []) ⟫ʷ
wl1396 c4 = lw0 c4 (CCZ234 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ234 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1397 : Complete 4 → ⟪ (K3 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ []) ⟫ʷ
wl1397 c4 = lw0 c4 (K3 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl

wl1398 : Complete 4 → ⟪ (CCZ124 ∷ CX31 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ124 ∷ []) ⟫ʷ
wl1398 c4 = lw0 c4 (CCZ124 ∷ CX31 ∷ CCZ234 ∷ []) (CX31 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1399 : Complete 4 → ⟪ (CCZ124 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CCZ124 ∷ []) ⟫ʷ
wl1399 c4 = lw0 c4 (CCZ124 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1400 : Complete 4 → ⟪ (CX31 ∷ CCZ234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
wl1400 c4 = lw0 c4 (CX31 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX31 ∷ []) tt tt Eq.refl

wl1401 : Complete 4 → ⟪ (CX13 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CX13 ∷ Toff201 ∷ []) ⟫ʷ
wl1401 c4 = lw4 c4 (CX13 ∷ Toff203 ∷ []) (Toff203 ∷ CX13 ∷ Toff201 ∷ []) tt tt Eq.refl

wl1402 : Complete 4 → ⟪ (CX13 ∷ Toff201 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
wl1402 c4 = lw4 c4 (CX13 ∷ Toff201 ∷ Toff201 ∷ []) (CX13 ∷ []) tt tt Eq.refl

wl1403 : Complete 4 → ⟪ (CCZ123 ∷ Toff312 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ []) ⟫ʷ
wl1403 c4 = lw4 c4 (CCZ123 ∷ Toff312 ∷ CZ12 ∷ []) (Toff312 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1404 : Complete 4 → ⟪ (CS34⁻ ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS34⁻ ∷ []) ⟫ʷ
wl1404 c4 = lw0 c4 (CS34⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl1405 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ []) ⟫ʷ
wl1405 c4 = lw0 c4 (CCZ134 ∷ []) (CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1406 : Complete 4 → ⟪ (CCZ124 ∷ CCZ134 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ134 ∷ []) ⟫ʷ
wl1406 c4 = lw0 c4 (CCZ124 ∷ CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1407 : Complete 4 → ⟪ (Toff012 ∷ Toff312 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff312 ∷ []) ⟫ʷ
wl1407 c4 = lw4 c4 (Toff012 ∷ Toff312 ∷ Toff023 ∷ []) (Toff023 ∷ Toff312 ∷ []) tt tt Eq.refl

wl1408 : Complete 4 → ⟪ (CCZ134 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ134 ∷ Toff312 ∷ []) ⟫ʷ
wl1408 c4 = lw0 c4 (CCZ134 ∷ CCZ124 ∷ []) (Toff312 ∷ CCZ134 ∷ Toff312 ∷ []) tt tt Eq.refl

wl1409 : Complete 4 → ⟪ (K2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl1409 c4 = lw0 c4 (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl1410 : Complete 4 → ⟪ (S3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl1410 c4 = lw0 c4 (S3 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl1411 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ []) ⟫ʷ
wl1411 c4 = lw1 c4 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) tt tt Eq.refl

wl1412 : Complete 4 → ⟪ (S1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl1412 c4 = lw0 c4 (S1 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl1413 : Complete 4 → ⟪ (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
wl1413 c4 = lw0 c4 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl

wl1414 : Complete 4 → ⟪ (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ []) ⟫ʷ
wl1414 c4 = lw0 c4 (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1415 : Complete 4 → ⟪ (CCZ124 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ CS12 ∷ []) ⟫ʷ
wl1415 c4 = lw0 c4 (CCZ124 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ []) (Toff324 ∷ CS13 ∷ CS12 ∷ []) tt tt Eq.refl

wl1416 : Complete 4 → ⟪ (CS12 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1416 c4 = lw0 c4 (CS12 ∷ []) (Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1417 : Complete 4 → ⟪ (K1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl1417 c4 = lw0 c4 (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl1418 : Complete 4 → ⟪ (S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl1418 c4 = lw0 c4 (S2 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl1419 : Complete 4 → ⟪ (K3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl1419 c4 = lw0 c4 (K3 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl1420 : Complete 4 → ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wl1420 c4 = lw4 c4 (K0 ∷ S0 ∷ S0 ∷ K0 ∷ ι ∷ []) (X0 ∷ []) tt tt Eq.refl

wl1421 : Complete 4 → ⟪ (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff213 ∷ []) ⟫ʷ
wl1421 c4 = lw4 c4 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (Toff301 ∷ Toff213 ∷ []) tt tt Eq.refl

wl1422 : Complete 4 → ⟪ (CS01⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS01⁻ ∷ []) ⟫ʷ
wl1422 c4 = lw4 c4 (CS01⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl1423 : Complete 4 → ⟪ (X0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1423 c4 = lw4 c4 (X0 ∷ X0 ∷ []) [] tt tt Eq.refl

wl1424 : Complete 4 → ⟪ (S0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S1 ∷ []) ⟫ʷ
wl1424 c4 = lw4 c4 (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) tt tt Eq.refl

wl1425 : Complete 4 → ⟪ (CK01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK10 ∷ []) ⟫ʷ
wl1425 c4 = lw4 c4 (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) tt tt Eq.refl

wl1426 : Complete 4 → ⟪ (S1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S2 ∷ []) ⟫ʷ
wl1426 c4 = lw4 c4 (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) tt tt Eq.refl

wl1427 : Complete 4 → ⟪ (CK20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK21 ∷ []) ⟫ʷ
wl1427 c4 = lw4 c4 (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) tt tt Eq.refl

wl1428 : Complete 4 → ⟪ (S2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ S3 ∷ []) ⟫ʷ
wl1428 c4 = lw4 c4 (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ []) tt tt Eq.refl

wl1429 : Complete 4 → ⟪ (S3 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ S4 ∷ []) ⟫ʷ
wl1429 c4 = lw0 c4 (S3 ∷ Sw34 ∷ []) (Sw34 ∷ S4 ∷ []) tt tt Eq.refl

wl1430 : Complete 4 → ⟪ (Toff213 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ Toff213 ∷ []) ⟫ʷ
wl1430 c4 = lw4 c4 (Toff213 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff213 ∷ []) tt tt Eq.refl

wl1431 : Complete 4 → ⟪ (X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ []) ⟫ʷ
wl1431 c4 = lw4 c4 (X0 ∷ S0 ∷ X0 ∷ []) (ι ∷ S0⁻ ∷ []) tt tt Eq.refl

wl1432 : Complete 4 → ⟪ (CZ24 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) ⟫ʷ
wl1432 c4 = lw0 c4 (CZ24 ∷ Toff213 ∷ []) (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1433 : Complete 4 → ⟪ (X0 ∷ CZ24 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wl1433 c4 = lw1 c4 (X0 ∷ CZ24 ∷ CZ24 ∷ []) (X0 ∷ []) tt tt Eq.refl

wl1434 : Complete 4 → ⟪ (CX13 ∷ Toff301 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff301 ∷ []) ⟫ʷ
wl1434 c4 = lw4 c4 (CX13 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ []) tt tt Eq.refl

wl1435 : Complete 4 → ⟪ (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff301 ∷ []) ⟫ʷ
wl1435 c4 = lw4 c4 (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (Toff213 ∷ Toff301 ∷ []) tt tt Eq.refl

wl1436 : Complete 4 → ⟪ (Toff301 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX13 ∷ Toff301 ∷ []) ⟫ʷ
wl1436 c4 = lw4 c4 (Toff301 ∷ X0 ∷ []) (X0 ∷ CX13 ∷ Toff301 ∷ []) tt tt Eq.refl

wl1437 : Complete 4 → ⟪ (CS34 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS34 ∷ []) ⟫ʷ
wl1437 c4 = lw1 c4 (CS34 ∷ X0 ∷ []) (X0 ∷ CS34 ∷ []) tt tt Eq.refl

wl1438 : Complete 4 → ⟪ (CS34⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS34⁻ ∷ []) ⟫ʷ
wl1438 c4 = lw1 c4 (CS34⁻ ∷ X0 ∷ []) (X0 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl1439 : Complete 4 → ⟪ (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) ⟫ʷ
wl1439 c4 = lw4 c4 (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) tt tt Eq.refl

wl1440 : Complete 4 → ⟪ (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ
wl1440 c4 = lw4 c4 (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) tt tt Eq.refl

wl1441 : Complete 4 → ⟪ (K1 ∷ CK01 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ []) ⟫ʷ
wl1441 c4 = lw4 c4 (K1 ∷ CK01 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ []) tt tt Eq.refl

wl1442 : Complete 4 → ⟪ (K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ K1 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ
wl1442 c4 = lw4 c4 (K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ []) (Toff201 ∷ K1 ∷ CK01 ∷ S0 ∷ []) tt tt Eq.refl

wl1443 : Complete 4 → ⟪ (CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ
wl1443 c4 = lw4 c4 (CK01 ∷ X0 ∷ []) (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ []) tt tt Eq.refl

wl1444 : Complete 4 → ⟪ (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ
wl1444 c4 = lw4 c4 (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) tt tt Eq.refl

wl1445 : Complete 4 → ⟪ (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wl1445 c4 = lw4 c4 (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wl1446 : Complete 4 → ⟪ (X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ X0 ∷ []) ⟫ʷ
wl1446 c4 = lw4 c4 (X0 ∷ S0 ∷ []) (ι ∷ S0⁻ ∷ X0 ∷ []) tt tt Eq.refl

wl1447 : Complete 4 → ⟪ (Toff213 ∷ ι ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ Toff213 ∷ []) ⟫ʷ
wl1447 c4 = lw4 c4 (Toff213 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff213 ∷ []) tt tt Eq.refl

wl1448 : Complete 4 → ⟪ (S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ ι ∷ S0⁻ ∷ []) ⟫ʷ
wl1448 c4 = lw4 c4 (S0 ∷ X0 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ []) tt tt Eq.refl

wl1449 : Complete 4 → ⟪ (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wl1449 c4 = lw4 c4 (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wl1450 : Complete 4 → ⟪ (CS01 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ
wl1450 c4 = lw4 c4 (CS01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS01 ∷ []) tt tt Eq.refl

wl1451 : Complete 4 → ⟪ (S1 ∷ CS01⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS01 ∷ []) ⟫ʷ
wl1451 c4 = lw4 c4 (S1 ∷ CS01⁻ ∷ X0 ∷ []) (X0 ∷ CS01 ∷ []) tt tt Eq.refl

wl1452 : Complete 4 → ⟪ (S1 ∷ CS01⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ S1 ∷ CS01⁻ ∷ []) ⟫ʷ
wl1452 c4 = lw4 c4 (S1 ∷ CS01⁻ ∷ Toff213 ∷ []) (Toff213 ∷ S1 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl1453 : Complete 4 → ⟪ (CS01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S1 ∷ CS01⁻ ∷ []) ⟫ʷ
wl1453 c4 = lw4 c4 (CS01 ∷ X0 ∷ []) (X0 ∷ S1 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wl1454 : Complete 4 → ⟪ (CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ
wl1454 c4 = lw4 c4 (CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS01 ∷ []) tt tt Eq.refl

wl1455 : Complete 4 → ⟪ (CS23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS23 ∷ []) ⟫ʷ
wl1455 c4 = lw4 c4 (CS23 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ []) tt tt Eq.refl

wl1456 : Complete 4 → ⟪ (Sw34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Sw34 ∷ []) ⟫ʷ
wl1456 c4 = lw0 c4 (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) tt tt Eq.refl

wl1457 : Complete 4 → ⟪ (Sw23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Sw23 ∷ []) ⟫ʷ
wl1457 c4 = lw4 c4 (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) tt tt Eq.refl

wl1458 : Complete 4 → ⟪ (Sw12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Sw12 ∷ []) ⟫ʷ
wl1458 c4 = lw4 c4 (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) tt tt Eq.refl

wl1459 : Complete 4 → ⟪ (Sw01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Sw01 ∷ []) ⟫ʷ
wl1459 c4 = lw4 c4 (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) tt tt Eq.refl

wl1460 : Complete 4 → ⟪ (K1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ
wl1460 c4 = lw4 c4 (K1 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) tt tt Eq.refl

wl1461 : Complete 4 → ⟪ (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ []) ⟫ʷ
wl1461 c4 = lw4 c4 (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (ι ∷ []) tt tt Eq.refl

wl1462 : Complete 4 → ⟪ (CS01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS01 ∷ []) ⟫ʷ
wl1462 c4 = lw4 c4 (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) tt tt Eq.refl

wl1463 : Complete 4 → ⟪ (CK41 ∷ S4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1463 c4 = lw0 c4 (CK41 ∷ S4 ∷ CK41 ∷ []) [] tt tt Eq.refl

wl1464 : Complete 4 → ⟪ (CK41 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1464 c4 = lw0 c4 (CK41 ∷ CK41 ∷ S4 ∷ []) [] tt tt Eq.refl

wl1465 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ012 ∷ CX03 ∷ []) ⟫ʷ
wl1465 c4 = lw4 c4 (CCZ012 ∷ []) (CX03 ∷ CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl

wl1466 : Complete 4 → ⟪ (CCZ134 ∷ Toff423 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ134 ∷ []) ⟫ʷ
wl1466 c4 = lw0 c4 (CCZ134 ∷ Toff423 ∷ CCZ123 ∷ []) (Toff423 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1467 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ123 ∷ CX30 ∷ []) ⟫ʷ
wl1467 c4 = lw4 c4 (CCZ123 ∷ []) (CX30 ∷ CCZ123 ∷ CX30 ∷ []) tt tt Eq.refl

wl1468 : Complete 4 → ⟪ (CCZ012 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ
wl1468 c4 = lw4 c4 (CCZ012 ∷ CX30 ∷ []) (CX30 ∷ CCZ123 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1469 : Complete 4 → ⟪ (CCZ123 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ
wl1469 c4 = lw4 c4 (CCZ123 ∷ CX03 ∷ []) (CX03 ∷ CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1470 : Complete 4 → ⟪ (CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wl1470 c4 = lw4 c4 (CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl

wl1471 : Complete 4 → ⟪ (K1 ∷ CK01 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ K1 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ
wl1471 c4 = lw4 c4 (K1 ∷ CK01 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ K1 ∷ CK01 ∷ S0 ∷ []) tt tt Eq.refl

wl1472 : Complete 4 → ⟪ (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ []) ⟫ʷ
wl1472 c4 = lw0 c4 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (Toff413 ∷ []) tt tt Eq.refl

wl1473 : Complete 4 → ⟪ (CS13⁻ ∷ S4 ∷ Toff413 ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ134 ∷ []) ⟫ʷ
wl1473 c4 = lw0 c4 (CS13⁻ ∷ S4 ∷ Toff413 ∷ S4⁻ ∷ []) (Toff413 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1474 : Complete 4 → ⟪ (Toff413 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1474 c4 = lw0 c4 (Toff413 ∷ Toff413 ∷ []) [] tt tt Eq.refl

wl1475 : Complete 4 → ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1475 c4 = lw4 c4 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1476 : Complete 4 → ⟪ (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ
wl1476 c4 = lw4 c4 (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ []) tt tt Eq.refl

wl1477 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ013 ∷ CX12 ∷ []) ⟫ʷ
wl1477 c4 = lw4 c4 (CCZ013 ∷ []) (CX12 ∷ CCZ013 ∷ CX12 ∷ []) tt tt Eq.refl

wl1478 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ023 ∷ CX21 ∷ []) ⟫ʷ
wl1478 c4 = lw4 c4 (CCZ023 ∷ []) (CX21 ∷ CCZ023 ∷ CX21 ∷ []) tt tt Eq.refl

wl1479 : Complete 4 → ⟪ (CCZ013 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ023 ∷ CCZ013 ∷ []) ⟫ʷ
wl1479 c4 = lw4 c4 (CCZ013 ∷ CX21 ∷ []) (CX21 ∷ CCZ023 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1480 : Complete 4 → ⟪ (CCZ023 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ013 ∷ CCZ023 ∷ []) ⟫ʷ
wl1480 c4 = lw4 c4 (CCZ023 ∷ CX12 ∷ []) (CX12 ∷ CCZ013 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1481 : Complete 4 → ⟪ (CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
wl1481 c4 = lw4 c4 (CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl

wl1482 : Complete 4 → ⟪ (CCZ134 ∷ CZ13 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ134 ∷ []) ⟫ʷ
wl1482 c4 = lw0 c4 (CCZ134 ∷ CZ13 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1483 : Complete 4 → ⟪ (CCZ134 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ134 ∷ Toff413 ∷ []) ⟫ʷ
wl1483 c4 = lw0 c4 (CCZ134 ∷ CZ13 ∷ []) (Toff413 ∷ CCZ134 ∷ Toff413 ∷ []) tt tt Eq.refl

wl1484 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ134 ∷ CZ13 ∷ []) ⟫ʷ
wl1484 c4 = lw0 c4 (CCZ134 ∷ []) (CZ13 ∷ CCZ134 ∷ CZ13 ∷ []) tt tt Eq.refl

wl1485 : Complete 4 → ⟪ (CCZ134 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ134 ∷ CZ13 ∷ []) ⟫ʷ
wl1485 c4 = lw0 c4 (CCZ134 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ134 ∷ CZ13 ∷ []) tt tt Eq.refl

wl1486 : Complete 4 → ⟪ (CCZ134 ∷ CZ13 ∷ Toff413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ []) ⟫ʷ
wl1486 c4 = lw0 c4 (CCZ134 ∷ CZ13 ∷ Toff413 ∷ CCZ134 ∷ []) (Toff413 ∷ []) tt tt Eq.refl

wl1487 : Complete 4 → ⟪ (K2 ∷ CK02 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ []) ⟫ʷ
wl1487 c4 = lw4 c4 (K2 ∷ CK02 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ []) tt tt Eq.refl

wl1488 : Complete 4 → ⟪ (K2 ∷ CK02 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ K2 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ
wl1488 c4 = lw4 c4 (K2 ∷ CK02 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ K2 ∷ CK02 ∷ S0 ∷ []) tt tt Eq.refl

wl1489 : Complete 4 → ⟪ (CCZ134 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CCZ134 ∷ []) ⟫ʷ
wl1489 c4 = lw0 c4 (CCZ134 ∷ K2 ∷ []) (K2 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1490 : Complete 4 → ⟪ (CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ K2 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ
wl1490 c4 = lw4 c4 (CK02 ∷ X0 ∷ []) (X0 ∷ K2 ∷ CK02 ∷ S0 ∷ []) tt tt Eq.refl

wl1491 : Complete 4 → ⟪ (CCZ234 ∷ CZ23 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ234 ∷ []) ⟫ʷ
wl1491 c4 = lw0 c4 (CCZ234 ∷ CZ23 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1492 : Complete 4 → ⟪ (CCZ234 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ234 ∷ Toff423 ∷ []) ⟫ʷ
wl1492 c4 = lw0 c4 (CCZ234 ∷ CZ23 ∷ []) (Toff423 ∷ CCZ234 ∷ Toff423 ∷ []) tt tt Eq.refl

wl1493 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ234 ∷ CZ23 ∷ []) ⟫ʷ
wl1493 c4 = lw0 c4 (CCZ234 ∷ []) (CZ23 ∷ CCZ234 ∷ CZ23 ∷ []) tt tt Eq.refl

wl1494 : Complete 4 → ⟪ (CCZ234 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ234 ∷ CZ23 ∷ []) ⟫ʷ
wl1494 c4 = lw0 c4 (CCZ234 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ234 ∷ CZ23 ∷ []) tt tt Eq.refl

wl1495 : Complete 4 → ⟪ (CCZ234 ∷ CZ23 ∷ Toff423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ []) ⟫ʷ
wl1495 c4 = lw0 c4 (CCZ234 ∷ CZ23 ∷ Toff423 ∷ CCZ234 ∷ []) (Toff423 ∷ []) tt tt Eq.refl

wl1496 : Complete 4 → ⟪ (CCZ134 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ134 ∷ CCZ123 ∷ []) ⟫ʷ
wl1496 c4 = lw0 c4 (CCZ134 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1497 : Complete 4 → ⟪ (CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wl1497 c4 = lw4 c4 (CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl

wl1498 : Complete 4 → ⟪ (CZ24 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) ⟫ʷ
wl1498 c4 = lw0 c4 (CZ24 ∷ Toff413 ∷ []) (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1499 : Complete 4 → ⟪ (CCZ123 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ123 ∷ []) ⟫ʷ
wl1499 c4 = lw0 c4 (CCZ123 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1500 : Complete 4 → ⟪ (CS13⁻ ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1500 c4 = lw0 c4 (CS13⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1501 : Complete 4 → ⟪ (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
wl1501 c4 = lw4 c4 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (Toff302 ∷ []) tt tt Eq.refl

wl1502 : Complete 4 → ⟪ (CS13 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS13 ∷ []) ⟫ʷ
wl1502 c4 = lw0 c4 (CS13 ∷ Toff413 ∷ []) (Toff413 ∷ CS13 ∷ []) tt tt Eq.refl

wl1503 : Complete 4 → ⟪ (CCZ123 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ []) ⟫ʷ
wl1503 c4 = lw4 c4 (CCZ123 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ []) (Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1504 : Complete 4 → ⟪ (CCZ012 ∷ CS13 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff302 ∷ CCZ012 ∷ []) ⟫ʷ
wl1504 c4 = lw4 c4 (CCZ012 ∷ CS13 ∷ Toff302 ∷ []) (CS13 ∷ Toff302 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1505 : Complete 4 → ⟪ (CX31 ∷ Toff103 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff103 ∷ []) ⟫ʷ
wl1505 c4 = lw4 c4 (CX31 ∷ Toff103 ∷ X0 ∷ []) (X0 ∷ Toff103 ∷ []) tt tt Eq.refl

wl1506 : Complete 4 → ⟪ (CX31 ∷ Toff103 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX31 ∷ Toff103 ∷ []) ⟫ʷ
wl1506 c4 = lw4 c4 (CX31 ∷ Toff103 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX31 ∷ Toff103 ∷ []) tt tt Eq.refl

wl1507 : Complete 4 → ⟪ (CX31 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CX31 ∷ []) ⟫ʷ
wl1507 c4 = lw0 c4 (CX31 ∷ Toff423 ∷ []) (Toff423 ∷ CX31 ∷ []) tt tt Eq.refl

wl1508 : Complete 4 → ⟪ (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ []) ⟫ʷ
wl1508 c4 = lw4 c4 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (Toff103 ∷ []) tt tt Eq.refl

wl1509 : Complete 4 → ⟪ (CS13 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS13 ∷ []) ⟫ʷ
wl1509 c4 = lw0 c4 (CS13 ∷ Toff423 ∷ []) (Toff423 ∷ CS13 ∷ []) tt tt Eq.refl

wl1510 : Complete 4 → ⟪ (Toff103 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX31 ∷ Toff103 ∷ []) ⟫ʷ
wl1510 c4 = lw4 c4 (Toff103 ∷ X0 ∷ []) (X0 ∷ CX31 ∷ Toff103 ∷ []) tt tt Eq.refl

wl1511 : Complete 4 → ⟪ (CS12 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS12 ∷ []) ⟫ʷ
wl1511 c4 = lw4 c4 (CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ []) tt tt Eq.refl

wl1512 : Complete 4 → ⟪ (CS12 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS12 ∷ []) ⟫ʷ
wl1512 c4 = lw4 c4 (CS12 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS12 ∷ []) tt tt Eq.refl

wl1513 : Complete 4 → ⟪ (CS12⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1513 c4 = lw4 c4 (CS12⁻ ∷ X0 ∷ []) (X0 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1514 : Complete 4 → ⟪ (CS12⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wl1514 c4 = lw4 c4 (CS12⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1515 : Complete 4 → ⟪ (K1 ∷ CK01 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ K1 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ
wl1515 c4 = lw4 c4 (K1 ∷ CK01 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ K1 ∷ CK01 ∷ S0 ∷ []) tt tt Eq.refl

wl1516 : Complete 4 → ⟪ (CZ14 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) ⟫ʷ
wl1516 c4 = lw0 c4 (CZ14 ∷ Toff423 ∷ []) (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1517 : Complete 4 → ⟪ (CS13⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1517 c4 = lw0 c4 (CS13⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1518 : Complete 4 → ⟪ (CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) ⟫ʷ
wl1518 c4 = lw4 c4 (CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) tt tt Eq.refl

wl1519 : Complete 4 → ⟪ (CCZ012 ∷ Toff302 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ CCZ012 ∷ []) ⟫ʷ
wl1519 c4 = lw4 c4 (CCZ012 ∷ Toff302 ∷ CS13 ∷ []) (Toff302 ∷ CS13 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl1520 : Complete 4 → ⟪ (CX23 ∷ Toff302 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff302 ∷ []) ⟫ʷ
wl1520 c4 = lw4 c4 (CX23 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ []) tt tt Eq.refl

wl1521 : Complete 4 → ⟪ (CX23 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX23 ∷ Toff302 ∷ []) ⟫ʷ
wl1521 c4 = lw4 c4 (CX23 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX23 ∷ Toff302 ∷ []) tt tt Eq.refl

wl1522 : Complete 4 → ⟪ (CX24 ∷ CX23 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CX23 ∷ []) ⟫ʷ
wl1522 c4 = lw0 c4 (CX24 ∷ CX23 ∷ Toff423 ∷ []) (Toff423 ∷ CX23 ∷ []) tt tt Eq.refl

wl1523 : Complete 4 → ⟪ (CX24 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CX24 ∷ []) ⟫ʷ
wl1523 c4 = lw0 c4 (CX24 ∷ Toff423 ∷ []) (Toff423 ∷ CX24 ∷ []) tt tt Eq.refl

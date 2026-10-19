------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
-- 
-- Part 2 of 5 of the proofs of Step4.Main's hypB that compute normal
-- forms, one lemma per relation of Step 3; in one module they took 41 s.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_ ; auto)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Presentation.Tactics.Lists
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open import Presentation.Tactics.Words

open Monoid-Equational
open Rewriting
open Associative
open InContext

open import Presentation.Tactics.Lists using (MaybeEq ; _=m?_ ; isJust ; fromJust)
open import Examples.Groups.Clifford+CS-3qubit.MaybeEq-Instances
open import Examples.Groups.Clifford+CS-3qubit.CosetNF
open import Examples.Groups.Clifford+CS-3qubit.Gate

import Examples.Groups.Clifford+CS-3qubit.Step3.Rel as L

open import Examples.Groups.Clifford+CS-3qubit.Step4.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8D
open import Examples.Groups.Clifford+CS-3qubit.Step4.KD
open import Examples.Groups.Clifford+CS-3qubit.Step4.Lemmas

open import Examples.Groups.Clifford+CS-3qubit.Step4.Simple

module Examples.Groups.Clifford+CS-3qubit.Step4.HypB2 where

  hb1308 : Goal L.ax-CCX0-CX12-CCX2-CCX0-Swap01=CX02-CCX0-CX01-CX12-CX10
  hb1308 = ListNF.listnfeq' nf-s7 auto

  hb1309 : Goal L.ax-CCX0-CX12-CCX0-Swap01=CX02-CX01-CX12-CX10
  hb1309 = ListNF.listnfeq' nf-s7 auto

  hb1310 : Goal L.ax-CCX0-CX21-CCX0-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX20-CCX0
  hb1310 = ListNF.listnfeq' nf-s7 auto

  hb1311 : Goal L.ax-CCX0-CX21-CCX0-CCX2-CX01=CX20-CX21-CCX2-CX01
  hb1311 = ListNF.listnfeq' nf-s7 auto

  hb1312 : Goal L.ax-CCX0-CX10-CX02-CCX1=CCX1-CCX0-CX12-Swap01-CX12-CX10
  hb1312 = ListNF.listnfeq' nf-s7 auto

  hb1313 : Goal L.ax-CCX0-CX10-CCX1=CCX1-CX10-CCX0
  hb1313 = ListNF.listnfeq' nf-s6 auto

  hb1314 : Goal L.ax-CCX0-CX10-CCX1-CX02=CCX1-CCX0-CX02-CX12-CX10
  hb1314 = ListNF.listnfeq' nf-s7 auto

  hb1315 : Goal L.ax-CCX0-CX10-CCX1-CCX2-CX01=CX10-CCX1-CCX2-CX01-CCX0
  hb1315 = ListNF.listnfeq' nf-s6 auto

  hb1316 : Goal L.ax-CCX0-CX10-CCX2-CCX1=CX20-CCX1-CCX2-CX12-CX21-CX10-CX20-CCX0
  hb1316 = ListNF.listnfeq' nf-s7 auto

  hb1317 : Goal L.ax-CCX0-CX10-CX12-CCX1=CX10-CX12-CCX1-CX10-CCX0
  hb1317 = ListNF.listnfeq' nf-s7 auto

  hb1318 : Goal L.ax-CCX0-CX10-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX21
  hb1318 = ListNF.listnfeq' nf-s7 auto

  hb1319 : Goal L.ax-CCX0-CX20-CX01-CCX2=CCX2-CCX0-CX12-Swap01-CX21-CX12-CX10
  hb1319 = ListNF.listnfeq' nf-s7 auto

  hb1320 : Goal L.ax-CCX0-CX20-CCX1-CCX2=CX10-CCX2-CCX1-CX21-CX12-CX10-CX20-CCX0
  hb1320 = ListNF.listnfeq' nf-s7 auto

  hb1321 : Goal L.ax-CCX0-CX20-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-CX20-CCX0
  hb1321 = ListNF.listnfeq' nf-s7 auto

  hb1322 : Goal L.ax-CCX0-CX20-CCX1-CCX2-CX01=CX20-CCX1-CCX2-CX01-CCX0
  hb1322 = ListNF.listnfeq' nf-s7 auto

  hb1323 : Goal L.ax-CCX0-CX20-CCX2=CCX2-CX20-CCX0
  hb1323 = ListNF.listnfeq' nf-s7 auto

  hb1324 : Goal L.ax-CCX0-CX20-CCX2-Swap01=CCX2-CCX0-Swap01-CX21
  hb1324 = ListNF.listnfeq' nf-s7 auto

  hb1325 : Goal L.ax-CCX0-CX20-CCX2-CX01=CCX2-CCX0-CX01-CX21-CX20
  hb1325 = ListNF.listnfeq' nf-s7 auto

  hb1326 : Goal L.ax-CCX0-CX20-CCX2-CX02=CX20-CCX2-CX02-CCX0
  hb1326 = ListNF.listnfeq' nf-s7 auto

  hb1327 : Goal L.ax-CCX0-CX20-CCX2-CCX1=CCX2-CX10-CCX1-CX21-CX10-CX20-CCX0
  hb1327 = ListNF.listnfeq' nf-s7 auto

  hb1328 : Goal L.ax-CCX0-CX20-CCX2-CCX1-CX01=CCX2-CCX1-CX01-CX20-CCX0
  hb1328 = ListNF.listnfeq' nf-s7 auto

  hb1329 : Goal L.ax-CCX0-CX20-CCX2-CCX1-CX02=CX20-CCX2-CCX1-CX02-CCX0
  hb1329 = ListNF.listnfeq' nf-s7 auto

  hb1330 : Goal L.ax-CCX0-CX20-CX21-CCX2-CX01=CX21-CCX0-CCX2-CX01
  hb1330 = ListNF.listnfeq' nf-s7 auto

  hb1331 : Goal L.ax-CCX0-CCX0-Swap01=Swap01
  hb1331 = ListNF.listnfeq' nf-s6 auto

  hb1332 : Goal L.ax-CCX0-CCX0-CX01=CX01
  hb1332 = ListNF.listnfeq' nf-s6 auto

  hb1333 : Goal L.ax-CCX0-CCX0-CX01-CCX2=CX01-CCX2
  hb1333 = ListNF.listnfeq' nf-s6 auto

  hb1334 : Goal L.ax-CCX0-CCX0-CX02=CX02
  hb1334 = ListNF.listnfeq' nf-s7 auto

  hb1335 : Goal L.ax-CCX0-CCX0-CX02-CCX1=CX02-CCX1
  hb1335 = ListNF.listnfeq' nf-s7 auto

  hb1336 : Goal L.ax-CCX0-CCX0-CCX1-CX02=CCX1-CX02
  hb1336 = ListNF.listnfeq' nf-s7 auto

  hb1337 : Goal L.ax-CCX0-CCX0-CCX1-CCX2=CCX1-CCX2
  hb1337 = ListNF.listnfeq' nf-s6 auto

  hb1338 : Goal L.ax-CCX0-CCX0-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01
  hb1338 = ListNF.listnfeq' nf-s6 auto

  hb1339 : Goal L.ax-CCX0-CCX0-CCX1-CX12-Swap01=CCX1-CX12-Swap01
  hb1339 = ListNF.listnfeq' nf-s7 auto

  hb1340 : Goal L.ax-CCX0-CCX0-CCX2-Swap01=CCX2-Swap01
  hb1340 = ListNF.listnfeq' nf-s6 auto

  hb1341 : Goal L.ax-CCX0-CCX0-CCX2-CCX1=CCX2-CCX1
  hb1341 = ListNF.listnfeq' nf-s6 auto

  hb1342 : Goal L.ax-CCX0-CCX0-CX12-Swap01=CX12-Swap01
  hb1342 = ListNF.listnfeq' nf-s7 auto

  hb1343 : Goal L.ax-CCX0-CCX0-CX12-CCX1-CX02=CX12-CCX1-CX02
  hb1343 = ListNF.listnfeq' nf-s7 auto

  hb1344 : Goal L.ax-CCX0-CCX0-CX12-CCX2-Swap01=CX12-CCX2-Swap01
  hb1344 = ListNF.listnfeq' nf-s7 auto

  hb1345 : Goal L.ax-CCX0-CCX0-CX21-CCX2-CX01=CX21-CCX2-CX01
  hb1345 = ListNF.listnfeq' nf-s7 auto

  hb1346 : Goal L.ax-CCX0-CCX0-Swap12-Swap01=Swap12-Swap01
  hb1346 = ListNF.listnfeq' nf-s7 auto

  hb1347 : Goal L.ax-CCX0-CCX0-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01
  hb1347 = ListNF.listnfeq' nf-s7 auto

  hb1348 : Goal L.ax-CCX0-CCX0-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01
  hb1348 = ListNF.listnfeq' nf-s7 auto

  hb1349 : Goal L.ax-iI-S0-K0-S0-CK10=S0-K0-S0-CK10-iI
  hb1349 = mvI.general-rewrite 20 auto

  hb1350 : Goal L.ax-iI-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-iI
  hb1350 = mvI.general-rewrite 20 auto

  hb1351 : Goal L.ax-iI-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-iI
  hb1351 = mvI.general-rewrite 20 auto

  hb1352 : Goal L.ax-iI-S0-K0-S0-CK20=S0-K0-S0-CK20-iI
  hb1352 = mvI.general-rewrite 20 auto

  hb1353 : Goal L.ax-iI-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-iI
  hb1353 = mvI.general-rewrite 20 auto

  hb1354 : Goal L.ax-iI-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-iI
  hb1354 = mvI.general-rewrite 20 auto

  hb1355 : Goal L.ax-iI-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-iI
  hb1355 = mvI.general-rewrite 20 auto

  hb1356 : Goal L.ax-iI-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-iI
  hb1356 = mvI.general-rewrite 20 auto

  hb1357 : Goal L.ax-iI-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-iI
  hb1357 = mvI.general-rewrite 20 auto

  hb1358 : Goal L.ax-iI-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-iI
  hb1358 = mvI.general-rewrite 20 auto

  hb1359 : Goal L.ax-iI-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-iI
  hb1359 = mvI.general-rewrite 20 auto

  hb1360 : Goal L.ax-iI-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-iI
  hb1360 = mvI.general-rewrite 20 auto

  hb1361 : Goal L.ax-iI-S0-K0-CK10=S0-K0-CK10-iI
  hb1361 = mvI.general-rewrite 20 auto

  hb1362 : Goal L.ax-iI-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-iI
  hb1362 = mvI.general-rewrite 20 auto

  hb1363 : Goal L.ax-iI-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-iI
  hb1363 = mvI.general-rewrite 20 auto

  hb1364 : Goal L.ax-iI-S0-K0-CK20=S0-K0-CK20-iI
  hb1364 = mvI.general-rewrite 20 auto

  hb1365 : Goal L.ax-iI-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-iI
  hb1365 = mvI.general-rewrite 20 auto

  hb1366 : Goal L.ax-iI-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-iI
  hb1366 = mvI.general-rewrite 20 auto

  hb1367 : Goal L.ax-iI-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-iI
  hb1367 = mvI.general-rewrite 20 auto

  hb1368 : Goal L.ax-iI-S0-K0-CK20-CK10=S0-K0-CK20-CK10-iI
  hb1368 = mvI.general-rewrite 20 auto

  hb1369 : Goal L.ax-iI-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-iI
  hb1369 = mvI.general-rewrite 20 auto

  hb1370 : Goal L.ax-iI-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-iI
  hb1370 = mvI.general-rewrite 20 auto

  hb1371 : Goal L.ax-iI-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-iI
  hb1371 = mvI.general-rewrite 20 auto

  hb1372 : Goal L.ax-iI-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-iI
  hb1372 = mvI.general-rewrite 20 auto

  hb1373 : Goal L.ax-iI-S0-K0-CCK'=S0-K0-CCK'-iI
  hb1373 = mvI.general-rewrite 20 auto

  hb1374 : Goal L.ax-iI-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-iI
  hb1374 = mvI.general-rewrite 20 auto

  hb1375 : Goal L.ax-iI-S0-CK10-CCK'=S0-CK10-CCK'-iI
  hb1375 = mvI.general-rewrite 20 auto

  hb1376 : Goal L.ax-iI-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-iI
  hb1376 = mvI.general-rewrite 20 auto

  hb1377 : Goal L.ax-iI-S0-CK20-S0-CK10=S0-CK20-S0-CK10-iI
  hb1377 = mvI.general-rewrite 20 auto

  hb1378 : Goal L.ax-iI-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-iI
  hb1378 = mvI.general-rewrite 20 auto

  hb1379 : Goal L.ax-iI-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-iI
  hb1379 = mvI.general-rewrite 20 auto

  hb1380 : Goal L.ax-iI-S0-CK20-CK10=S0-CK20-CK10-iI
  hb1380 = mvI.general-rewrite 20 auto

  hb1381 : Goal L.ax-iI-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-iI
  hb1381 = mvI.general-rewrite 20 auto

  hb1382 : Goal L.ax-iI-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-iI
  hb1382 = mvI.general-rewrite 20 auto

  hb1383 : Goal L.ax-iI-S0-CK20-CCK'=S0-CK20-CCK'-iI
  hb1383 = mvI.general-rewrite 20 auto

  hb1384 : Goal L.ax-iI-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-iI
  hb1384 = mvI.general-rewrite 20 auto

  hb1385 : Goal L.ax-iI-K0-S0-CK10=K0-S0-CK10-iI
  hb1385 = mvI.general-rewrite 20 auto

  hb1386 : Goal L.ax-iI-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-iI
  hb1386 = mvI.general-rewrite 20 auto

  hb1387 : Goal L.ax-iI-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-iI
  hb1387 = mvI.general-rewrite 20 auto

  hb1388 : Goal L.ax-iI-K0-S0-CK20=K0-S0-CK20-iI
  hb1388 = mvI.general-rewrite 20 auto

  hb1389 : Goal L.ax-iI-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-iI
  hb1389 = mvI.general-rewrite 20 auto

  hb1390 : Goal L.ax-iI-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-iI
  hb1390 = mvI.general-rewrite 20 auto

  hb1391 : Goal L.ax-iI-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-iI
  hb1391 = mvI.general-rewrite 20 auto

  hb1392 : Goal L.ax-iI-K0-S0-CK20-CK10=K0-S0-CK20-CK10-iI
  hb1392 = mvI.general-rewrite 20 auto

  hb1393 : Goal L.ax-iI-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-iI
  hb1393 = mvI.general-rewrite 20 auto

  hb1394 : Goal L.ax-iI-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-iI
  hb1394 = mvI.general-rewrite 20 auto

  hb1395 : Goal L.ax-iI-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-iI
  hb1395 = mvI.general-rewrite 20 auto

  hb1396 : Goal L.ax-iI-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-iI
  hb1396 = mvI.general-rewrite 20 auto

  hb1397 : Goal L.ax-iI-K0-CK10=K0-CK10-iI
  hb1397 = mvI.general-rewrite 20 auto

  hb1398 : Goal L.ax-iI-K0-CK10-CCK'=K0-CK10-CCK'-iI
  hb1398 = mvI.general-rewrite 20 auto

  hb1399 : Goal L.ax-iI-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-iI
  hb1399 = mvI.general-rewrite 20 auto

  hb1400 : Goal L.ax-iI-K0-CK20=K0-CK20-iI
  hb1400 = mvI.general-rewrite 20 auto

  hb1401 : Goal L.ax-iI-K0-CK20-S0-CK10=K0-CK20-S0-CK10-iI
  hb1401 = mvI.general-rewrite 20 auto

  hb1402 : Goal L.ax-iI-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-iI
  hb1402 = mvI.general-rewrite 20 auto

  hb1403 : Goal L.ax-iI-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-iI
  hb1403 = mvI.general-rewrite 20 auto

  hb1404 : Goal L.ax-iI-K0-CK20-CK10=K0-CK20-CK10-iI
  hb1404 = mvI.general-rewrite 20 auto

  hb1405 : Goal L.ax-iI-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-iI
  hb1405 = mvI.general-rewrite 20 auto

  hb1406 : Goal L.ax-iI-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-iI
  hb1406 = mvI.general-rewrite 20 auto

  hb1407 : Goal L.ax-iI-K0-CK20-CCK'=K0-CK20-CCK'-iI
  hb1407 = mvI.general-rewrite 20 auto

  hb1408 : Goal L.ax-iI-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-iI
  hb1408 = mvI.general-rewrite 20 auto

  hb1409 : Goal L.ax-iI-K0-CCK'=K0-CCK'-iI
  hb1409 = mvI.general-rewrite 20 auto

  hb1410 : Goal L.ax-iI-K0-CCK'-CCK'=K0-CCK'-CCK'-iI
  hb1410 = mvI.general-rewrite 20 auto

  hb1411 : Goal L.ax-iI-CK10-CCK'=CK10-CCK'-iI
  hb1411 = mvI.general-rewrite 20 auto

  hb1412 : Goal L.ax-iI-CK10-CCK'-CCK'=CK10-CCK'-CCK'-iI
  hb1412 = mvI.general-rewrite 20 auto

  hb1413 : Goal L.ax-iI-CK20-S0-CK10=CK20-S0-CK10-iI
  hb1413 = mvI.general-rewrite 20 auto

  hb1414 : Goal L.ax-iI-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-iI
  hb1414 = mvI.general-rewrite 20 auto

  hb1415 : Goal L.ax-iI-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-iI
  hb1415 = mvI.general-rewrite 20 auto

  hb1416 : Goal L.ax-iI-CK20-CK10=CK20-CK10-iI
  hb1416 = mvI.general-rewrite 20 auto

  hb1417 : Goal L.ax-iI-CK20-CK10-CCK'=CK20-CK10-CCK'-iI
  hb1417 = mvI.general-rewrite 20 auto

  hb1418 : Goal L.ax-iI-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-iI
  hb1418 = mvI.general-rewrite 20 auto

  hb1419 : Goal L.ax-iI-CK20-CCK'=CK20-CCK'-iI
  hb1419 = mvI.general-rewrite 20 auto

  hb1420 : Goal L.ax-iI-CK20-CCK'-CCK'=CK20-CCK'-CCK'-iI
  hb1420 = mvI.general-rewrite 20 auto

  hb1421 : Goal L.ax-S0-S0-K0-S0-CK10=K0-S0-CK10-X0-S0-S0-S1-S1-iI-iI-iI
  hb1421 = ListNF.listnfeq' nf-e4 auto

  hb1422 : Goal L.ax-S0-S0-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-X0-S0-S0-S1-S1-CS12-CS12-CS12-CCZ-iI-iI-iI
  hb1422 = ListNF.listnfeq' nf-e4 auto

  hb1423 : Goal L.ax-S0-S0-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-CS12-CS12-CS12-iI-iI-iI
  hb1423 = ListNF.listnfeq' nf-e4 auto

  hb1424 : Goal L.ax-S0-S0-K0-S0-CK20=K0-S0-CK20-X0-S0-S0-S2-S2-iI-iI-iI
  hb1424 = ListNF.listnfeq' nf-e4 auto

  hb1425 : Goal L.ax-S0-S0-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-X0-CX10-S2-S2-CS01-CS01-iI-iI
  hb1425 = ListNF.listnfeq' nf-e4 auto

  hb1426 : Goal L.ax-S0-S0-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CS12-iI-iI
  hb1426 = ListNF.listnfeq' nf-e4 auto

  hb1427 : Goal L.ax-S0-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CCZ-iI-iI
  hb1427 = ListNF.listnfeq' nf-e4 auto

  hb1428 : Goal L.ax-S0-S0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-X0-S0-S0-S1-S1-S2-S2-iI-iI-iI
  hb1428 = ListNF.listnfeq' nf-e4 auto

  hb1429 : Goal L.ax-S0-S0-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-X0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-CCZ-iI-iI-iI
  hb1429 = ListNF.listnfeq' nf-e4 auto

  hb1430 : Goal L.ax-S0-S0-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-iI-iI-iI
  hb1430 = ListNF.listnfeq' nf-e4 auto

  hb1431 : Goal L.ax-S0-S0-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-X0-S0-S0-S2-S2-CS12-CS12-CS12-CCZ-iI-iI-iI
  hb1431 = ListNF.listnfeq' nf-e4 auto

  hb1432 : Goal L.ax-S0-S0-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-X0-CCX0-S0-S0-S2-S2-CS12-CS12-CS12-iI-iI-iI
  hb1432 = ListNF.listnfeq' nf-e4 auto

  hb1433 : Goal L.ax-S0-S0-K0-CK10=K0-CK10-X0-CX10-CS01-CS01
  hb1433 = ListNF.listnfeq' nf-e4 auto

  hb1434 : Goal L.ax-S0-S0-K0-CK10-CCK'=K0-CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12
  hb1434 = ListNF.listnfeq' nf-e4 auto

  hb1435 : Goal L.ax-S0-S0-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ
  hb1435 = ListNF.listnfeq' nf-e4 auto

  hb1436 : Goal L.ax-S0-S0-K0-CK20=K0-CK20-X0-CX20-CS02-CS02
  hb1436 = ListNF.listnfeq' nf-e4 auto

  hb1437 : Goal L.ax-S0-S0-K0-CK20-S0-CK10=K0-CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI-iI
  hb1437 = ListNF.listnfeq' nf-e4 auto

  hb1438 : Goal L.ax-S0-S0-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI-iI
  hb1438 = ListNF.listnfeq' nf-e4 auto

  hb1439 : Goal L.ax-S0-S0-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI-iI
  hb1439 = ListNF.listnfeq' nf-e4 auto

  hb1440 : Goal L.ax-S0-S0-K0-CK20-CK10=K0-CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02
  hb1440 = ListNF.listnfeq' nf-e4 auto

  hb1441 : Goal L.ax-S0-S0-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ
  hb1441 = ListNF.listnfeq' nf-e4 auto

  hb1442 : Goal L.ax-S0-S0-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ
  hb1442 = ListNF.listnfeq' nf-e4 auto

  hb1443 : Goal L.ax-S0-S0-K0-CK20-CCK'=K0-CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12
  hb1443 = ListNF.listnfeq' nf-e4 auto

  hb1444 : Goal L.ax-S0-S0-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ
  hb1444 = ListNF.listnfeq' nf-e4 auto

  hb1445 : Goal L.ax-S0-S0-K0-CCK'=K0-CCK'-X0-CCX0-CCZ
  hb1445 = ListNF.listnfeq' nf-e4 auto

  hb1446 : Goal L.ax-S0-S0-K0-CCK'-CCK'=K0-CCK'-CCK'-X0-CS12-CCZ
  hb1446 = ListNF.listnfeq' nf-e4 auto

  hb1447 : Goal L.ax-S0-S0-CK10-CCK'=CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CCZ
  hb1447 = ListNF.listnfeq' nf-e3 auto

  hb1448 : Goal L.ax-S0-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX10-S0-S0-CS01-CS01-CS12-CCZ
  hb1448 = ListNF.listnfeq' nf-e3 auto

  hb1449 : Goal L.ax-S0-S0-CK20-S0-CK10=CK20-S0-CK10-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ
  hb1449 = ListNF.listnfeq' nf-e3 auto

  hb1450 : Goal L.ax-S0-S0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12
  hb1450 = ListNF.listnfeq' nf-e3 auto

  hb1451 : Goal L.ax-S0-S0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CX10-CX20-S0-S0-S2-S2-S2-CS01-CS01-CS12-CCZ
  hb1451 = ListNF.listnfeq' nf-e3 auto

  hb1452 : Goal L.ax-S0-S0-CK20-CK10=CK20-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02
  hb1452 = ListNF.listnfeq' nf-e3 auto

  hb1453 : Goal L.ax-S0-S0-CK20-CK10-CCK'=CK20-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12
  hb1453 = ListNF.listnfeq' nf-e3 auto

  hb1454 : Goal L.ax-S0-S0-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ
  hb1454 = ListNF.listnfeq' nf-e3 auto

  hb1455 : Goal L.ax-S0-S0-CK20-CCK'=CK20-CCK'-CX20-CCX0-S0-S0-CS02-CS02-CCZ
  hb1455 = ListNF.listnfeq' nf-e3 auto

  hb1456 : Goal L.ax-S0-S0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CX20-S0-S0-CS02-CS02-CS12-CCZ
  hb1456 = ListNF.listnfeq' nf-e3 auto

  hb1457 : Goal L.ax-S1-S0-K0-S0-CK10=S0-K0-S0-CK10-S1
  hb1457 = mvD3.general-rewrite 50 auto

  hb1458 : Goal L.ax-S1-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-S1
  hb1458 = mvD3.general-rewrite 50 auto

  hb1459 : Goal L.ax-S1-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-S1
  hb1459 = mvD3.general-rewrite 50 auto

  hb1460 : Goal L.ax-S1-S0-K0-S0-CK20=S0-K0-S0-CK20-S1
  hb1460 = mvD3.general-rewrite 50 auto

  hb1461 : Goal L.ax-S1-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-S1
  hb1461 = mvD3.general-rewrite 50 auto

  hb1462 : Goal L.ax-S1-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-S1
  hb1462 = mvD3.general-rewrite 50 auto

  hb1463 : Goal L.ax-S1-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-S1
  hb1463 = mvD3.general-rewrite 50 auto

  hb1464 : Goal L.ax-S1-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-S1
  hb1464 = mvD3.general-rewrite 50 auto

  hb1465 : Goal L.ax-S1-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-S1
  hb1465 = mvD3.general-rewrite 50 auto

  hb1466 : Goal L.ax-S1-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-S1
  hb1466 = mvD3.general-rewrite 50 auto

  hb1467 : Goal L.ax-S1-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-S1
  hb1467 = mvD3.general-rewrite 50 auto

  hb1468 : Goal L.ax-S1-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-S1
  hb1468 = mvD3.general-rewrite 50 auto

  hb1469 : Goal L.ax-S1-S0-K0-CK10=S0-K0-CK10-S1
  hb1469 = mvD3.general-rewrite 50 auto

  hb1470 : Goal L.ax-S1-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-S1
  hb1470 = mvD3.general-rewrite 50 auto

  hb1471 : Goal L.ax-S1-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-S1
  hb1471 = mvD3.general-rewrite 50 auto

  hb1472 : Goal L.ax-S1-S0-K0-CK20=S0-K0-CK20-S1
  hb1472 = mvD3.general-rewrite 50 auto

  hb1473 : Goal L.ax-S1-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-S1
  hb1473 = mvD3.general-rewrite 50 auto

  hb1474 : Goal L.ax-S1-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-S1
  hb1474 = mvD3.general-rewrite 50 auto

  hb1475 : Goal L.ax-S1-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-S1
  hb1475 = mvD3.general-rewrite 50 auto

  hb1476 : Goal L.ax-S1-S0-K0-CK20-CK10=S0-K0-CK20-CK10-S1
  hb1476 = mvD3.general-rewrite 50 auto

  hb1477 : Goal L.ax-S1-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-S1
  hb1477 = mvD3.general-rewrite 50 auto

  hb1478 : Goal L.ax-S1-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-S1
  hb1478 = mvD3.general-rewrite 50 auto

  hb1479 : Goal L.ax-S1-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-S1
  hb1479 = mvD3.general-rewrite 50 auto

  hb1480 : Goal L.ax-S1-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-S1
  hb1480 = mvD3.general-rewrite 50 auto

  hb1481 : Goal L.ax-S1-S0-K0-CCK'=S0-K0-CCK'-S1
  hb1481 = mvD3.general-rewrite 50 auto

  hb1482 : Goal L.ax-S1-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-S1
  hb1482 = mvD3.general-rewrite 50 auto

  hb1483 : Goal L.ax-S1-S0-CK10-CCK'=S0-CK10-CCK'-S1
  hb1483 = mvD3.general-rewrite 50 auto

  hb1484 : Goal L.ax-S1-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-S1
  hb1484 = mvD3.general-rewrite 50 auto

  hb1485 : Goal L.ax-S1-S0-CK20-S0-CK10=S0-CK20-S0-CK10-S1
  hb1485 = mvD3.general-rewrite 50 auto

  hb1486 : Goal L.ax-S1-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-S1
  hb1486 = mvD3.general-rewrite 50 auto

  hb1487 : Goal L.ax-S1-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-S1
  hb1487 = mvD3.general-rewrite 50 auto

  hb1488 : Goal L.ax-S1-S0-CK20-CK10=S0-CK20-CK10-S1
  hb1488 = mvD3.general-rewrite 50 auto

  hb1489 : Goal L.ax-S1-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-S1
  hb1489 = mvD3.general-rewrite 50 auto

  hb1490 : Goal L.ax-S1-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-S1
  hb1490 = mvD3.general-rewrite 50 auto

  hb1491 : Goal L.ax-S1-S0-CK20-CCK'=S0-CK20-CCK'-S1
  hb1491 = mvD3.general-rewrite 50 auto

  hb1492 : Goal L.ax-S1-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-S1
  hb1492 = mvD3.general-rewrite 50 auto

  hb1493 : Goal L.ax-S1-K0-S0-CK10=K0-S0-CK10-S1
  hb1493 = mvD3.general-rewrite 50 auto

  hb1494 : Goal L.ax-S1-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-S1
  hb1494 = mvD3.general-rewrite 50 auto

  hb1495 : Goal L.ax-S1-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-S1
  hb1495 = mvD3.general-rewrite 50 auto

  hb1496 : Goal L.ax-S1-K0-S0-CK20=K0-S0-CK20-S1
  hb1496 = mvD3.general-rewrite 50 auto

  hb1497 : Goal L.ax-S1-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-S1
  hb1497 = mvD3.general-rewrite 50 auto

  hb1498 : Goal L.ax-S1-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-S1
  hb1498 = mvD3.general-rewrite 50 auto

  hb1499 : Goal L.ax-S1-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-S1
  hb1499 = mvD3.general-rewrite 50 auto

  hb1500 : Goal L.ax-S1-K0-S0-CK20-CK10=K0-S0-CK20-CK10-S1
  hb1500 = mvD3.general-rewrite 50 auto

  hb1501 : Goal L.ax-S1-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-S1
  hb1501 = mvD3.general-rewrite 50 auto

  hb1502 : Goal L.ax-S1-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-S1
  hb1502 = mvD3.general-rewrite 50 auto

  hb1503 : Goal L.ax-S1-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-S1
  hb1503 = mvD3.general-rewrite 50 auto

  hb1504 : Goal L.ax-S1-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-S1
  hb1504 = mvD3.general-rewrite 50 auto

  hb1505 : Goal L.ax-S1-K0-CK10=K0-CK10-S1
  hb1505 = mvD3.general-rewrite 50 auto

  hb1506 : Goal L.ax-S1-K0-CK10-CCK'=K0-CK10-CCK'-S1
  hb1506 = mvD3.general-rewrite 50 auto

  hb1507 : Goal L.ax-S1-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-S1
  hb1507 = mvD3.general-rewrite 50 auto

  hb1508 : Goal L.ax-S1-K0-CK20=K0-CK20-S1
  hb1508 = mvD3.general-rewrite 50 auto

  hb1509 : Goal L.ax-S1-K0-CK20-S0-CK10=K0-CK20-S0-CK10-S1
  hb1509 = mvD3.general-rewrite 50 auto

  hb1510 : Goal L.ax-S1-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-S1
  hb1510 = mvD3.general-rewrite 50 auto

  hb1511 : Goal L.ax-S1-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-S1
  hb1511 = mvD3.general-rewrite 50 auto

  hb1512 : Goal L.ax-S1-K0-CK20-CK10=K0-CK20-CK10-S1
  hb1512 = mvD3.general-rewrite 50 auto

  hb1513 : Goal L.ax-S1-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-S1
  hb1513 = mvD3.general-rewrite 50 auto

  hb1514 : Goal L.ax-S1-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-S1
  hb1514 = mvD3.general-rewrite 50 auto

  hb1515 : Goal L.ax-S1-K0-CK20-CCK'=K0-CK20-CCK'-S1
  hb1515 = mvD3.general-rewrite 50 auto

  hb1516 : Goal L.ax-S1-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-S1
  hb1516 = mvD3.general-rewrite 50 auto

  hb1517 : Goal L.ax-S1-K0-CCK'=K0-CCK'-S1
  hb1517 = mvD3.general-rewrite 50 auto

  hb1518 : Goal L.ax-S1-K0-CCK'-CCK'=K0-CCK'-CCK'-S1
  hb1518 = mvD3.general-rewrite 50 auto

  hb1519 : Goal L.ax-S1-CK10-CCK'=CK10-CCK'-S1
  hb1519 = mvD3.general-rewrite 50 auto

  hb1520 : Goal L.ax-S1-CK10-CCK'-CCK'=CK10-CCK'-CCK'-S1
  hb1520 = mvD3.general-rewrite 50 auto

  hb1521 : Goal L.ax-S1-CK20-S0-CK10=CK20-S0-CK10-S1
  hb1521 = mvD3.general-rewrite 50 auto

  hb1522 : Goal L.ax-S1-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-S1
  hb1522 = mvD3.general-rewrite 50 auto

  hb1523 : Goal L.ax-S1-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-S1
  hb1523 = mvD3.general-rewrite 50 auto

  hb1524 : Goal L.ax-S1-CK20-CK10=CK20-CK10-S1
  hb1524 = mvD3.general-rewrite 50 auto

  hb1525 : Goal L.ax-S1-CK20-CK10-CCK'=CK20-CK10-CCK'-S1
  hb1525 = mvD3.general-rewrite 50 auto

  hb1526 : Goal L.ax-S1-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-S1
  hb1526 = mvD3.general-rewrite 50 auto

  hb1527 : Goal L.ax-S1-CK20-CCK'=CK20-CCK'-S1
  hb1527 = mvD3.general-rewrite 50 auto

  hb1528 : Goal L.ax-S1-CK20-CCK'-CCK'=CK20-CCK'-CCK'-S1
  hb1528 = mvD3.general-rewrite 50 auto

  hb1529 : Goal L.ax-S2-S0-K0-S0-CK10=S0-K0-S0-CK10-S2
  hb1529 = mvD3.general-rewrite 50 auto

  hb1530 : Goal L.ax-S2-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-S2
  hb1530 = mvD3.general-rewrite 50 auto

  hb1531 : Goal L.ax-S2-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-S2
  hb1531 = mvD3.general-rewrite 50 auto

  hb1532 : Goal L.ax-S2-S0-K0-S0-CK20=S0-K0-S0-CK20-S2
  hb1532 = mvD3.general-rewrite 50 auto

  hb1533 : Goal L.ax-S2-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-S2
  hb1533 = mvD3.general-rewrite 50 auto

  hb1534 : Goal L.ax-S2-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-S2
  hb1534 = mvD3.general-rewrite 50 auto

  hb1535 : Goal L.ax-S2-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-S2
  hb1535 = mvD3.general-rewrite 50 auto

  hb1536 : Goal L.ax-S2-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-S2
  hb1536 = mvD3.general-rewrite 50 auto

  hb1537 : Goal L.ax-S2-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-S2
  hb1537 = mvD3.general-rewrite 50 auto

  hb1538 : Goal L.ax-S2-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-S2
  hb1538 = mvD3.general-rewrite 50 auto

  hb1539 : Goal L.ax-S2-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-S2
  hb1539 = mvD3.general-rewrite 50 auto

  hb1540 : Goal L.ax-S2-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-S2
  hb1540 = mvD3.general-rewrite 50 auto

  hb1541 : Goal L.ax-S2-S0-K0-CK10=S0-K0-CK10-S2
  hb1541 = mvD3.general-rewrite 50 auto

  hb1542 : Goal L.ax-S2-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-S2
  hb1542 = mvD3.general-rewrite 50 auto

  hb1543 : Goal L.ax-S2-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-S2
  hb1543 = mvD3.general-rewrite 50 auto

  hb1544 : Goal L.ax-S2-S0-K0-CK20=S0-K0-CK20-S2
  hb1544 = mvD3.general-rewrite 50 auto

  hb1545 : Goal L.ax-S2-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-S2
  hb1545 = mvD3.general-rewrite 50 auto

  hb1546 : Goal L.ax-S2-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-S2
  hb1546 = mvD3.general-rewrite 50 auto

  hb1547 : Goal L.ax-S2-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-S2
  hb1547 = mvD3.general-rewrite 50 auto

  hb1548 : Goal L.ax-S2-S0-K0-CK20-CK10=S0-K0-CK20-CK10-S2
  hb1548 = mvD3.general-rewrite 50 auto

  hb1549 : Goal L.ax-S2-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-S2
  hb1549 = mvD3.general-rewrite 50 auto

  hb1550 : Goal L.ax-S2-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-S2
  hb1550 = mvD3.general-rewrite 50 auto

  hb1551 : Goal L.ax-S2-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-S2
  hb1551 = mvD3.general-rewrite 50 auto

  hb1552 : Goal L.ax-S2-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-S2
  hb1552 = mvD3.general-rewrite 50 auto

  hb1553 : Goal L.ax-S2-S0-K0-CCK'=S0-K0-CCK'-S2
  hb1553 = mvD3.general-rewrite 50 auto

  hb1554 : Goal L.ax-S2-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-S2
  hb1554 = mvD3.general-rewrite 50 auto

  hb1555 : Goal L.ax-S2-S0-CK10-CCK'=S0-CK10-CCK'-S2
  hb1555 = mvD3.general-rewrite 50 auto

  hb1556 : Goal L.ax-S2-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-S2
  hb1556 = mvD3.general-rewrite 50 auto

  hb1557 : Goal L.ax-S2-S0-CK20-S0-CK10=S0-CK20-S0-CK10-S2
  hb1557 = mvD3.general-rewrite 50 auto

  hb1558 : Goal L.ax-S2-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-S2
  hb1558 = mvD3.general-rewrite 50 auto

  hb1559 : Goal L.ax-S2-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-S2
  hb1559 = mvD3.general-rewrite 50 auto

  hb1560 : Goal L.ax-S2-S0-CK20-CK10=S0-CK20-CK10-S2
  hb1560 = mvD3.general-rewrite 50 auto

  hb1561 : Goal L.ax-S2-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-S2
  hb1561 = mvD3.general-rewrite 50 auto

  hb1562 : Goal L.ax-S2-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-S2
  hb1562 = mvD3.general-rewrite 50 auto

  hb1563 : Goal L.ax-S2-S0-CK20-CCK'=S0-CK20-CCK'-S2
  hb1563 = mvD3.general-rewrite 50 auto

  hb1564 : Goal L.ax-S2-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-S2
  hb1564 = mvD3.general-rewrite 50 auto

  hb1565 : Goal L.ax-S2-K0-S0-CK10=K0-S0-CK10-S2
  hb1565 = mvD3.general-rewrite 50 auto

  hb1566 : Goal L.ax-S2-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-S2
  hb1566 = mvD3.general-rewrite 50 auto

  hb1567 : Goal L.ax-S2-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-S2
  hb1567 = mvD3.general-rewrite 50 auto

  hb1568 : Goal L.ax-S2-K0-S0-CK20=K0-S0-CK20-S2
  hb1568 = mvD3.general-rewrite 50 auto

  hb1569 : Goal L.ax-S2-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-S2
  hb1569 = mvD3.general-rewrite 50 auto

  hb1570 : Goal L.ax-S2-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-S2
  hb1570 = mvD3.general-rewrite 50 auto

  hb1571 : Goal L.ax-S2-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-S2
  hb1571 = mvD3.general-rewrite 50 auto

  hb1572 : Goal L.ax-S2-K0-S0-CK20-CK10=K0-S0-CK20-CK10-S2
  hb1572 = mvD3.general-rewrite 50 auto

  hb1573 : Goal L.ax-S2-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-S2
  hb1573 = mvD3.general-rewrite 50 auto

  hb1574 : Goal L.ax-S2-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-S2
  hb1574 = mvD3.general-rewrite 50 auto

  hb1575 : Goal L.ax-S2-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-S2
  hb1575 = mvD3.general-rewrite 50 auto

  hb1576 : Goal L.ax-S2-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-S2
  hb1576 = mvD3.general-rewrite 50 auto

  hb1577 : Goal L.ax-S2-K0-CK10=K0-CK10-S2
  hb1577 = mvD3.general-rewrite 50 auto

  hb1578 : Goal L.ax-S2-K0-CK10-CCK'=K0-CK10-CCK'-S2
  hb1578 = mvD3.general-rewrite 50 auto

  hb1579 : Goal L.ax-S2-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-S2
  hb1579 = mvD3.general-rewrite 50 auto

  hb1580 : Goal L.ax-S2-K0-CK20=K0-CK20-S2
  hb1580 = mvD3.general-rewrite 50 auto

  hb1581 : Goal L.ax-S2-K0-CK20-S0-CK10=K0-CK20-S0-CK10-S2
  hb1581 = mvD3.general-rewrite 50 auto

  hb1582 : Goal L.ax-S2-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-S2
  hb1582 = mvD3.general-rewrite 50 auto

  hb1583 : Goal L.ax-S2-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-S2
  hb1583 = mvD3.general-rewrite 50 auto

  hb1584 : Goal L.ax-S2-K0-CK20-CK10=K0-CK20-CK10-S2
  hb1584 = mvD3.general-rewrite 50 auto

  hb1585 : Goal L.ax-S2-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-S2
  hb1585 = mvD3.general-rewrite 50 auto

  hb1586 : Goal L.ax-S2-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-S2
  hb1586 = mvD3.general-rewrite 50 auto

  hb1587 : Goal L.ax-S2-K0-CK20-CCK'=K0-CK20-CCK'-S2
  hb1587 = mvD3.general-rewrite 50 auto

  hb1588 : Goal L.ax-S2-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-S2
  hb1588 = mvD3.general-rewrite 50 auto

  hb1589 : Goal L.ax-S2-K0-CCK'=K0-CCK'-S2
  hb1589 = mvD3.general-rewrite 50 auto

  hb1590 : Goal L.ax-S2-K0-CCK'-CCK'=K0-CCK'-CCK'-S2
  hb1590 = mvD3.general-rewrite 50 auto

  hb1591 : Goal L.ax-S2-CK10-CCK'=CK10-CCK'-S2
  hb1591 = mvD3.general-rewrite 50 auto

  hb1592 : Goal L.ax-S2-CK10-CCK'-CCK'=CK10-CCK'-CCK'-S2
  hb1592 = mvD3.general-rewrite 50 auto

  hb1593 : Goal L.ax-S2-CK20-S0-CK10=CK20-S0-CK10-S2
  hb1593 = mvD3.general-rewrite 50 auto

  hb1594 : Goal L.ax-S2-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-S2
  hb1594 = mvD3.general-rewrite 50 auto

  hb1595 : Goal L.ax-S2-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-S2
  hb1595 = mvD3.general-rewrite 50 auto

  hb1596 : Goal L.ax-S2-CK20-CK10=CK20-CK10-S2
  hb1596 = mvD3.general-rewrite 50 auto

  hb1597 : Goal L.ax-S2-CK20-CK10-CCK'=CK20-CK10-CCK'-S2
  hb1597 = mvD3.general-rewrite 50 auto

  hb1598 : Goal L.ax-S2-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-S2
  hb1598 = mvD3.general-rewrite 50 auto

  hb1599 : Goal L.ax-S2-CK20-CCK'=CK20-CCK'-S2
  hb1599 = mvD3.general-rewrite 50 auto

  hb1600 : Goal L.ax-S2-CK20-CCK'-CCK'=CK20-CCK'-CCK'-S2
  hb1600 = mvD3.general-rewrite 50 auto

  hb1601 : Goal L.ax-CS01-S0-K0-S0-CK10=S0-K0-S0-CS01-CS01
  hb1601 = ListNF.listnfeq' nf-e4 auto

  hb1602 : Goal L.ax-CS01-S0-K0-S0-CK10-CCK'=S0-K0-CCK'-CCK'-CCX0-S0-CS01-CS01-CS12
  hb1602 = ListNF.listnfeq' nf-e4 auto

  hb1603 : Goal L.ax-CS01-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CCK'-S0-CS01-CS01-CS12-CS12-CS12-CCZ
  hb1603 = ListNF.listnfeq' nf-e4 auto

  hb1604 : Goal L.ax-CS01-S0-K0-S0-CK20=S0-K0-S0-CK20-CK10-CX10-CCX0-S1-CCZ
  hb1604 = ListNF.listnfeq' nf-e4 auto

  hb1605 : Goal L.ax-CS01-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-S1-CS01-CS01-CS01-CS12-CS12-CS12-CCZ
  hb1605 = ListNF.listnfeq' nf-e4 auto

  hb1606 : Goal L.ax-CS01-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-S1-CS01-CS01-CS01
  hb1606 = ListNF.listnfeq' nf-e4 auto

  hb1607 : Goal L.ax-CS01-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCX0-S1-CS01-CS01-CS01-CS12-CS12-CS12
  hb1607 = ListNF.listnfeq' nf-e4 auto

  hb1608 : Goal L.ax-CS01-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CCX0-CS01-CS01-CCZ
  hb1608 = ListNF.listnfeq' nf-e4 auto

  hb1609 : Goal L.ax-CS01-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CCK'-CS01-CS01
  hb1609 = ListNF.listnfeq' nf-e4 auto

  hb1610 : Goal L.ax-CS01-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCX0-CS01-CS01-CS12
  hb1610 = ListNF.listnfeq' nf-e4 auto

  hb1611 : Goal L.ax-CS01-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CK10-CCK'-CX10-S1-CS12-CCZ
  hb1611 = ListNF.listnfeq' nf-e4 auto

  hb1612 : Goal L.ax-CS01-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX10-S1
  hb1612 = ListNF.listnfeq' nf-e4 auto

  hb1613 : Goal L.ax-CS01-S0-K0-CK10=S0-K0-CK10-CS01
  hb1613 = ListNF.listnfeq' nf-e4 auto

  hb1614 : Goal L.ax-CS01-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CCK'-CS01-CS12-CCZ
  hb1614 = ListNF.listnfeq' nf-e4 auto

  hb1615 : Goal L.ax-CS01-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCX0-CS01-CCZ
  hb1615 = ListNF.listnfeq' nf-e4 auto

  hb1616 : Goal L.ax-CS01-S0-K0-CK20=S0-K0-CK20-S0-CK10-CCK'-CX10-CCX0-S0-S0-S0-S1-CCZ
  hb1616 = ListNF.listnfeq' nf-e4 auto

  hb1617 : Goal L.ax-CS01-S0-K0-CK20-S0-CK10=S0-K0-CK20-CCK'-CCX0-S0-CS01-CS01-CS12
  hb1617 = ListNF.listnfeq' nf-e4 auto

  hb1618 : Goal L.ax-CS01-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CS01-CS01-CS12-CS12-CS12-CCZ
  hb1618 = ListNF.listnfeq' nf-e4 auto

  hb1619 : Goal L.ax-CS01-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-S0-CS01-CS01
  hb1619 = ListNF.listnfeq' nf-e4 auto

  hb1620 : Goal L.ax-CS01-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCK'-CCK'-CCX0-CS01-CS12-CS12-CCZ
  hb1620 = ListNF.listnfeq' nf-e4 auto

  hb1621 : Goal L.ax-CS01-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CS01
  hb1621 = ListNF.listnfeq' nf-e4 auto

  hb1622 : Goal L.ax-CS01-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CS01-CS12-CS12-CS12-CCZ
  hb1622 = ListNF.listnfeq' nf-e4 auto

  hb1623 : Goal L.ax-CS01-S0-K0-CK20-CCK'=S0-K0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-S1-CS12-CS12-CS12
  hb1623 = ListNF.listnfeq' nf-e4 auto

  hb1624 : Goal L.ax-CS01-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CX10-S0-S0-S0-S1
  hb1624 = ListNF.listnfeq' nf-e4 auto

  hb1625 : Goal L.ax-CS01-S0-K0-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-S0-S1-CCZ
  hb1625 = ListNF.listnfeq' nf-e4 auto

  hb1626 : Goal L.ax-CS01-S0-K0-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CX10-CCX0-S0-S0-S0-S1-CS12-CS12-CS12
  hb1626 = ListNF.listnfeq' nf-e4 auto

  hb1627 : Goal L.ax-CS01-S0-CK10-CCK'=CK10-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CCZ
  hb1627 = ListNF.listnfeq' nf-e3 auto

  hb1628 : Goal L.ax-CS01-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX10-S0-CS01-CS01-CS01-CS12-CCZ
  hb1628 = ListNF.listnfeq' nf-e3 auto

  hb1629 : Goal L.ax-CS01-S0-CK20=S0-CK20-CCK'-CCK'-CCX0-CS01-CS12-CS12-CCZ
  hb1629 = ListNF.listnfeq' nf-e3 auto

  hb1630 : Goal L.ax-CS01-S0-CK20-S0-CK10=S0-CK20-CK10-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CS12
  hb1630 = ListNF.listnfeq' nf-e3 auto

  hb1631 : Goal L.ax-CS01-S0-CK20-S0-CK10-CCK'=S0-CK20-CK10-CCK'-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CS12
  hb1631 = ListNF.listnfeq' nf-e3 auto

  hb1632 : Goal L.ax-CS01-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CK10-CX10-CCX0-S0-CS01-CS01-CS01-CS12-CS12-CS12
  hb1632 = ListNF.listnfeq' nf-e3 auto

  hb1633 : Goal L.ax-CS01-S0-CK20-CK10=S0-CK20-S0-CK10-CCK'-CCK'-S0-S0-S0-CS01-CS12-CCZ
  hb1633 = ListNF.listnfeq' nf-e3 auto

  hb1634 : Goal L.ax-CS01-S0-CK20-CK10-CCK'=S0-CK20-S0-CK10-CCX0-S0-S0-S0-CS01-CCZ
  hb1634 = ListNF.listnfeq' nf-e3 auto

  hb1635 : Goal L.ax-CS01-S0-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCX0-S0-S0-S0-CS01-CS12-CS12-CS12
  hb1635 = ListNF.listnfeq' nf-e3 auto

  hb1636 : Goal L.ax-CS01-S0-CK20-CCK'=S0-CK20-CCK'-CS01
  hb1636 = ListNF.listnfeq' nf-e3 auto

  hb1637 : Goal L.ax-CS01-S0-CK20-CCK'-CCK'=S0-CK20-CS01-CS12-CS12-CS12-CCZ
  hb1637 = ListNF.listnfeq' nf-e3 auto

  hb1638 : Goal L.ax-CS01-K0-S0-CK10=K0-S0-CS01-CS01
  hb1638 = ListNF.listnfeq' nf-e4 auto

  hb1639 : Goal L.ax-CS01-K0-S0-CK10-CCK'=K0-CCK'-CCK'-CCX0-S0-CS01-CS01-CS12
  hb1639 = ListNF.listnfeq' nf-e4 auto

  hb1640 : Goal L.ax-CS01-K0-S0-CK10-CCK'-CCK'=K0-CCK'-S0-CS01-CS01-CS12-CS12-CS12-CCZ
  hb1640 = ListNF.listnfeq' nf-e4 auto

  hb1641 : Goal L.ax-CS01-K0-S0-CK20=K0-S0-CK20-CK10-CX10-CCX0-S1-CCZ
  hb1641 = ListNF.listnfeq' nf-e4 auto

  hb1642 : Goal L.ax-CS01-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-S1-CS01-CS01-CS01-CS12-CS12-CS12-CCZ
  hb1642 = ListNF.listnfeq' nf-e4 auto

  hb1643 : Goal L.ax-CS01-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-S1-CS01-CS01-CS01
  hb1643 = ListNF.listnfeq' nf-e4 auto

  hb1644 : Goal L.ax-CS01-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCX0-S1-CS01-CS01-CS01-CS12-CS12-CS12
  hb1644 = ListNF.listnfeq' nf-e4 auto

  hb1645 : Goal L.ax-CS01-K0-S0-CK20-CK10=K0-S0-CK20-CCX0-CS01-CS01-CCZ
  hb1645 = ListNF.listnfeq' nf-e4 auto

  hb1646 : Goal L.ax-CS01-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CCK'-CS01-CS01
  hb1646 = ListNF.listnfeq' nf-e4 auto

  hb1647 : Goal L.ax-CS01-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CCX0-CS01-CS01-CS12
  hb1647 = ListNF.listnfeq' nf-e4 auto

  hb1648 : Goal L.ax-CS01-K0-S0-CK20-CCK'=K0-S0-CK20-CK10-CCK'-CX10-S1-CS12-CCZ
  hb1648 = ListNF.listnfeq' nf-e4 auto

  hb1649 : Goal L.ax-CS01-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX10-S1
  hb1649 = ListNF.listnfeq' nf-e4 auto

  hb1650 : Goal L.ax-CS01-K0-CK10=K0-CK10-CS01
  hb1650 = ListNF.listnfeq' nf-e4 auto

  hb1651 : Goal L.ax-CS01-K0-CK10-CCK'=K0-CK10-CCK'-CCK'-CS01-CS12-CCZ
  hb1651 = ListNF.listnfeq' nf-e4 auto

  hb1652 : Goal L.ax-CS01-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCX0-CS01-CCZ
  hb1652 = ListNF.listnfeq' nf-e4 auto

  hb1653 : Goal L.ax-CS01-K0-CK20=K0-CK20-S0-CK10-CCK'-CX10-CCX0-S0-S0-S0-S1-CCZ
  hb1653 = ListNF.listnfeq' nf-e4 auto

  hb1654 : Goal L.ax-CS01-K0-CK20-S0-CK10=K0-CK20-CCK'-CCX0-S0-CS01-CS01-CS12
  hb1654 = ListNF.listnfeq' nf-e4 auto

  hb1655 : Goal L.ax-CS01-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CS01-CS01-CS12-CS12-CS12-CCZ
  hb1655 = ListNF.listnfeq' nf-e4 auto

  hb1656 : Goal L.ax-CS01-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-CCK'-CCK'-S0-CS01-CS01
  hb1656 = ListNF.listnfeq' nf-e4 auto

  hb1657 : Goal L.ax-CS01-K0-CK20-CK10=K0-CK20-CK10-CCK'-CCK'-CCX0-CS01-CS12-CS12-CCZ
  hb1657 = ListNF.listnfeq' nf-e4 auto

  hb1658 : Goal L.ax-CS01-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CS01
  hb1658 = ListNF.listnfeq' nf-e4 auto

  hb1659 : Goal L.ax-CS01-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CS01-CS12-CS12-CS12-CCZ
  hb1659 = ListNF.listnfeq' nf-e4 auto

  hb1660 : Goal L.ax-CS01-K0-CK20-CCK'=K0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-S1-CS12-CS12-CS12
  hb1660 = ListNF.listnfeq' nf-e4 auto

  hb1661 : Goal L.ax-CS01-K0-CK20-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX10-S0-S0-S0-S1
  hb1661 = ListNF.listnfeq' nf-e4 auto

  hb1662 : Goal L.ax-CS01-K0-CCK'=K0-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-S0-S1-CCZ
  hb1662 = ListNF.listnfeq' nf-e4 auto

  hb1663 : Goal L.ax-CS01-K0-CCK'-CCK'=K0-S0-CK10-CCK'-CX10-CCX0-S0-S0-S0-S1-CS12-CS12-CS12
  hb1663 = ListNF.listnfeq' nf-e4 auto

  hb1664 : Goal L.ax-CS01-CK10-CCK'=S0-CK10-CCK'-S0-S0-S0-CS01
  hb1664 = ListNF.listnfeq' nf-e3 auto

  hb1665 : Goal L.ax-CS01-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-S0-S0-S0-CS01
  hb1665 = ListNF.listnfeq' nf-e3 auto

  hb1666 : Goal L.ax-CS01-CK20=CK20-CCK'-CCK'-CCX0-CS01-CS12-CS12-CCZ
  hb1666 = ListNF.listnfeq' nf-e3 auto

  hb1667 : Goal L.ax-CS01-CK20-S0-CK10=CK20-CK10-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CS12
  hb1667 = ListNF.listnfeq' nf-e3 auto

  hb1668 : Goal L.ax-CS01-CK20-S0-CK10-CCK'=CK20-CK10-CCK'-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CS12
  hb1668 = ListNF.listnfeq' nf-e3 auto

  hb1669 : Goal L.ax-CS01-CK20-S0-CK10-CCK'-CCK'=CK20-CK10-CX10-CCX0-S0-CS01-CS01-CS01-CS12-CS12-CS12
  hb1669 = ListNF.listnfeq' nf-e3 auto

  hb1670 : Goal L.ax-CS01-CK20-CK10=CK20-S0-CK10-CCK'-CCK'-S0-S0-S0-CS01-CS12-CCZ
  hb1670 = ListNF.listnfeq' nf-e3 auto

  hb1671 : Goal L.ax-CS01-CK20-CK10-CCK'=CK20-S0-CK10-CCX0-S0-S0-S0-CS01-CCZ
  hb1671 = ListNF.listnfeq' nf-e3 auto

  hb1672 : Goal L.ax-CS01-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCX0-S0-S0-S0-CS01-CS12-CS12-CS12
  hb1672 = ListNF.listnfeq' nf-e3 auto

  hb1673 : Goal L.ax-CS01-CK20-CCK'=CK20-CCK'-CS01
  hb1673 = ListNF.listnfeq' nf-e3 auto

  hb1674 : Goal L.ax-CS01-CK20-CCK'-CCK'=CK20-CS01-CS12-CS12-CS12-CCZ
  hb1674 = ListNF.listnfeq' nf-e3 auto

  hb1675 : Goal L.ax-CS02-S0-K0-S0-CK10=S0-K0-S0-CK20-CK10-CX20-CCX0-S2-CCZ
  hb1675 = ListNF.listnfeq' nf-e4 auto

  hb1676 : Goal L.ax-CS02-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CX20-S2-CS12-CCZ
  hb1676 = ListNF.listnfeq' nf-e4 auto

  hb1677 : Goal L.ax-CS02-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX20-S2
  hb1677 = ListNF.listnfeq' nf-e4 auto

  hb1678 : Goal L.ax-CS02-S0-K0-S0-CK20=S0-K0-S0-CS02-CS02
  hb1678 = ListNF.listnfeq' nf-e4 auto

  hb1679 : Goal L.ax-CS02-S0-K0-S0-CK20-S0-CK10=S0-K0-CK10-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ
  hb1679 = ListNF.listnfeq' nf-e4 auto

  hb1680 : Goal L.ax-CS02-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ
  hb1680 = ListNF.listnfeq' nf-e4 auto

  hb1681 : Goal L.ax-CS02-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ
  hb1681 = ListNF.listnfeq' nf-e4 auto

  hb1682 : Goal L.ax-CS02-S0-K0-S0-CK20-CK10=S0-K0-S0-CK10-CCX0-CS02-CS02-CCZ
  hb1682 = ListNF.listnfeq' nf-e4 auto

  hb1683 : Goal L.ax-CS02-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK10-CCK'-CS02-CS02
  hb1683 = ListNF.listnfeq' nf-e4 auto

  hb1684 : Goal L.ax-CS02-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12
  hb1684 = ListNF.listnfeq' nf-e4 auto

  hb1685 : Goal L.ax-CS02-S0-K0-S0-CK20-CCK'=S0-K0-CCK'-CCK'-CCX0-S0-CS02-CS02-CS12
  hb1685 = ListNF.listnfeq' nf-e4 auto

  hb1686 : Goal L.ax-CS02-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CCK'-S0-CS02-CS02-CS12-CS12-CS12-CCZ
  hb1686 = ListNF.listnfeq' nf-e4 auto

  hb1687 : Goal L.ax-CS02-S0-K0-CK10=S0-K0-S0-CK20-S0-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02
  hb1687 = ListNF.listnfeq' nf-e4 auto

  hb1688 : Goal L.ax-CS02-S0-K0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12
  hb1688 = ListNF.listnfeq' nf-e4 auto

  hb1689 : Goal L.ax-CS02-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ
  hb1689 = ListNF.listnfeq' nf-e4 auto

  hb1690 : Goal L.ax-CS02-S0-K0-CK20=S0-K0-CK20-CS02
  hb1690 = ListNF.listnfeq' nf-e4 auto

  hb1691 : Goal L.ax-CS02-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ
  hb1691 = ListNF.listnfeq' nf-e4 auto

  hb1692 : Goal L.ax-CS02-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CS02
  hb1692 = ListNF.listnfeq' nf-e4 auto

  hb1693 : Goal L.ax-CS02-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CS02-CS12-CS12-CS12-CCZ
  hb1693 = ListNF.listnfeq' nf-e4 auto

  hb1694 : Goal L.ax-CS02-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ
  hb1694 = ListNF.listnfeq' nf-e4 auto

  hb1695 : Goal L.ax-CS02-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CS02
  hb1695 = ListNF.listnfeq' nf-e4 auto

  hb1696 : Goal L.ax-CS02-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CS02-CS12-CS12-CS12-CCZ
  hb1696 = ListNF.listnfeq' nf-e4 auto

  hb1697 : Goal L.ax-CS02-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CCK'-CS02-CS12-CCZ
  hb1697 = ListNF.listnfeq' nf-e4 auto

  hb1698 : Goal L.ax-CS02-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCX0-CS02-CCZ
  hb1698 = ListNF.listnfeq' nf-e4 auto

  hb1699 : Goal L.ax-CS02-S0-K0-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CX20-CCX0-S0-S0-S0-S2-CCZ
  hb1699 = ListNF.listnfeq' nf-e4 auto

  hb1700 : Goal L.ax-CS02-S0-K0-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CX20-CCX0-S0-S0-S0-S2-CS12-CS12-CS12
  hb1700 = ListNF.listnfeq' nf-e4 auto

  hb1701 : Goal L.ax-CS02-S0-CK10=S0-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ
  hb1701 = ListNF.listnfeq' nf-e3 auto

  hb1702 : Goal L.ax-CS02-S0-CK10-CCK'=S0-CK10-CCK'-CS02
  hb1702 = ListNF.listnfeq' nf-e3 auto

  hb1703 : Goal L.ax-CS02-S0-CK10-CCK'-CCK'=S0-CK10-CS02-CS12-CS12-CS12-CCZ
  hb1703 = ListNF.listnfeq' nf-e3 auto

  hb1704 : Goal L.ax-CS02-S0-CK20-S0-CK10=CK20-CK10-CCK'-CCK'-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12
  hb1704 = ListNF.listnfeq' nf-e3 auto

  hb1705 : Goal L.ax-CS02-S0-CK20-S0-CK10-CCK'=CK20-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12
  hb1705 = ListNF.listnfeq' nf-e3 auto

  hb1706 : Goal L.ax-CS02-S0-CK20-S0-CK10-CCK'-CCK'=CK20-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ
  hb1706 = ListNF.listnfeq' nf-e3 auto

  hb1707 : Goal L.ax-CS02-S0-CK20-CK10=CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CCZ
  hb1707 = ListNF.listnfeq' nf-e3 auto

  hb1708 : Goal L.ax-CS02-S0-CK20-CK10-CCK'=CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS12-CCZ
  hb1708 = ListNF.listnfeq' nf-e3 auto

  hb1709 : Goal L.ax-CS02-S0-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CS12
  hb1709 = ListNF.listnfeq' nf-e3 auto

  hb1710 : Goal L.ax-CS02-S0-CK20-CCK'=CK20-CCK'-CX20-CCX0-S0-CS02-CS02-CS02-CCZ
  hb1710 = ListNF.listnfeq' nf-e3 auto

  hb1711 : Goal L.ax-CS02-S0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CX20-S0-CS02-CS02-CS02-CS12-CCZ
  hb1711 = ListNF.listnfeq' nf-e3 auto

  hb1712 : Goal L.ax-CS02-K0-S0-CK10=K0-S0-CK20-CK10-CX20-CCX0-S2-CCZ
  hb1712 = ListNF.listnfeq' nf-e4 auto

  hb1713 : Goal L.ax-CS02-K0-S0-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX20-S2-CS12-CCZ
  hb1713 = ListNF.listnfeq' nf-e4 auto

  hb1714 : Goal L.ax-CS02-K0-S0-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX20-S2
  hb1714 = ListNF.listnfeq' nf-e4 auto

  hb1715 : Goal L.ax-CS02-K0-S0-CK20=K0-S0-CS02-CS02
  hb1715 = ListNF.listnfeq' nf-e4 auto

  hb1716 : Goal L.ax-CS02-K0-S0-CK20-S0-CK10=K0-CK10-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ
  hb1716 = ListNF.listnfeq' nf-e4 auto

  hb1717 : Goal L.ax-CS02-K0-S0-CK20-S0-CK10-CCK'=K0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ
  hb1717 = ListNF.listnfeq' nf-e4 auto

  hb1718 : Goal L.ax-CS02-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ
  hb1718 = ListNF.listnfeq' nf-e4 auto

  hb1719 : Goal L.ax-CS02-K0-S0-CK20-CK10=K0-S0-CK10-CCX0-CS02-CS02-CCZ
  hb1719 = ListNF.listnfeq' nf-e4 auto

  hb1720 : Goal L.ax-CS02-K0-S0-CK20-CK10-CCK'=K0-S0-CK10-CCK'-CS02-CS02
  hb1720 = ListNF.listnfeq' nf-e4 auto

  hb1721 : Goal L.ax-CS02-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12
  hb1721 = ListNF.listnfeq' nf-e4 auto

  hb1722 : Goal L.ax-CS02-K0-S0-CK20-CCK'=K0-CCK'-CCK'-CCX0-S0-CS02-CS02-CS12
  hb1722 = ListNF.listnfeq' nf-e4 auto

  hb1723 : Goal L.ax-CS02-K0-S0-CK20-CCK'-CCK'=K0-CCK'-S0-CS02-CS02-CS12-CS12-CS12-CCZ
  hb1723 = ListNF.listnfeq' nf-e4 auto

  hb1724 : Goal L.ax-CS02-K0-CK10=K0-S0-CK20-S0-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02
  hb1724 = ListNF.listnfeq' nf-e4 auto

  hb1725 : Goal L.ax-CS02-K0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12
  hb1725 = ListNF.listnfeq' nf-e4 auto

  hb1726 : Goal L.ax-CS02-K0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ
  hb1726 = ListNF.listnfeq' nf-e4 auto

  hb1727 : Goal L.ax-CS02-K0-CK20=K0-CK20-CS02
  hb1727 = ListNF.listnfeq' nf-e4 auto

  hb1728 : Goal L.ax-CS02-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ
  hb1728 = ListNF.listnfeq' nf-e4 auto

  hb1729 : Goal L.ax-CS02-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CS02
  hb1729 = ListNF.listnfeq' nf-e4 auto

  hb1730 : Goal L.ax-CS02-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CS02-CS12-CS12-CS12-CCZ
  hb1730 = ListNF.listnfeq' nf-e4 auto

  hb1731 : Goal L.ax-CS02-K0-CK20-CK10=K0-CK20-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ
  hb1731 = ListNF.listnfeq' nf-e4 auto

  hb1732 : Goal L.ax-CS02-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CS02
  hb1732 = ListNF.listnfeq' nf-e4 auto

  hb1733 : Goal L.ax-CS02-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CS02-CS12-CS12-CS12-CCZ
  hb1733 = ListNF.listnfeq' nf-e4 auto

  hb1734 : Goal L.ax-CS02-K0-CK20-CCK'=K0-CK20-CCK'-CCK'-CS02-CS12-CCZ
  hb1734 = ListNF.listnfeq' nf-e4 auto

  hb1735 : Goal L.ax-CS02-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCX0-CS02-CCZ
  hb1735 = ListNF.listnfeq' nf-e4 auto

  hb1736 : Goal L.ax-CS02-K0-CCK'=K0-S0-CK20-CCK'-CCK'-CX20-CCX0-S0-S0-S0-S2-CCZ
  hb1736 = ListNF.listnfeq' nf-e4 auto

  hb1737 : Goal L.ax-CS02-K0-CCK'-CCK'=K0-S0-CK20-CCK'-CX20-CCX0-S0-S0-S0-S2-CS12-CS12-CS12
  hb1737 = ListNF.listnfeq' nf-e4 auto

  hb1738 : Goal L.ax-CS02-CK10=CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ
  hb1738 = ListNF.listnfeq' nf-p24k0d auto

  hb1739 : Goal L.ax-CS02-CK10-CCK'=CK10-CCK'-CS02
  hb1739 = ListNF.listnfeq' nf-e3 auto

  hb1740 : Goal L.ax-CS02-CK10-CCK'-CCK'=CK10-CS02-CS12-CS12-CS12-CCZ
  hb1740 = ListNF.listnfeq' nf-e3 auto

  hb1741 : Goal L.ax-CS02-CK20-S0-CK10=S0-CK20-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ
  hb1741 = ListNF.listnfeq' nf-e3 auto

  hb1742 : Goal L.ax-CS02-CK20-S0-CK10-CCK'=S0-CK20-CK10-CCK'-CS02
  hb1742 = ListNF.listnfeq' nf-e3 auto

  hb1743 : Goal L.ax-CS02-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CK10-CS02-CS12-CS12-CS12-CCZ
  hb1743 = ListNF.listnfeq' nf-e3 auto

  hb1744 : Goal L.ax-CS02-CK20-CK10=S0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS12
  hb1744 = ListNF.listnfeq' nf-e3 auto

  hb1745 : Goal L.ax-CS02-CK20-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CCZ
  hb1745 = ListNF.listnfeq' nf-e3 auto

  hb1746 : Goal L.ax-CS02-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CX10-S0-S0-CS01-CS01-CS02-CS12-CS12-CS12-CCZ
  hb1746 = ListNF.listnfeq' nf-e3 auto

  hb1747 : Goal L.ax-CS02-CK20-CCK'=S0-CK20-CCK'-S0-S0-S0-CS02
  hb1747 = ListNF.listnfeq' nf-e3 auto

  hb1748 : Goal L.ax-CS02-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-S0-S0-S0-CS02
  hb1748 = ListNF.listnfeq' nf-e3 auto

  hb1749 : Goal L.ax-CS12-S0-K0-S0-CK10=S0-K0-S0-CK10-CS12
  hb1749 = mvD3.general-rewrite 50 auto

  hb1750 : Goal L.ax-CS12-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CS12
  hb1750 = mvD3.general-rewrite 50 auto

  hb1751 : Goal L.ax-CS12-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CS12
  hb1751 = mvD3.general-rewrite 50 auto

  hb1752 : Goal L.ax-CS12-S0-K0-S0-CK20=S0-K0-S0-CK20-CS12
  hb1752 = mvD3.general-rewrite 50 auto

  hb1753 : Goal L.ax-CS12-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CS12
  hb1753 = mvD3.general-rewrite 50 auto

  hb1754 : Goal L.ax-CS12-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CS12
  hb1754 = mvD3.general-rewrite 50 auto

  hb1755 : Goal L.ax-CS12-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CS12
  hb1755 = mvD3.general-rewrite 50 auto

  hb1756 : Goal L.ax-CS12-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CS12
  hb1756 = mvD3.general-rewrite 50 auto

  hb1757 : Goal L.ax-CS12-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CS12
  hb1757 = mvD3.general-rewrite 50 auto

  hb1758 : Goal L.ax-CS12-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CS12
  hb1758 = mvD3.general-rewrite 50 auto

  hb1759 : Goal L.ax-CS12-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CS12
  hb1759 = mvD3.general-rewrite 50 auto

  hb1760 : Goal L.ax-CS12-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CS12
  hb1760 = mvD3.general-rewrite 50 auto

  hb1761 : Goal L.ax-CS12-S0-K0-CK10=S0-K0-CK10-CS12
  hb1761 = mvD3.general-rewrite 50 auto

  hb1762 : Goal L.ax-CS12-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CS12
  hb1762 = mvD3.general-rewrite 50 auto

  hb1763 : Goal L.ax-CS12-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CS12
  hb1763 = mvD3.general-rewrite 50 auto

  hb1764 : Goal L.ax-CS12-S0-K0-CK20=S0-K0-CK20-CS12
  hb1764 = mvD3.general-rewrite 50 auto

  hb1765 : Goal L.ax-CS12-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CS12
  hb1765 = mvD3.general-rewrite 50 auto

  hb1766 : Goal L.ax-CS12-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CS12
  hb1766 = mvD3.general-rewrite 50 auto

  hb1767 : Goal L.ax-CS12-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CS12
  hb1767 = mvD3.general-rewrite 50 auto

  hb1768 : Goal L.ax-CS12-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CS12
  hb1768 = mvD3.general-rewrite 50 auto

  hb1769 : Goal L.ax-CS12-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CS12
  hb1769 = mvD3.general-rewrite 50 auto

  hb1770 : Goal L.ax-CS12-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CS12
  hb1770 = mvD3.general-rewrite 50 auto

  hb1771 : Goal L.ax-CS12-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CS12
  hb1771 = mvD3.general-rewrite 50 auto

  hb1772 : Goal L.ax-CS12-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CS12
  hb1772 = mvD3.general-rewrite 50 auto

  hb1773 : Goal L.ax-CS12-S0-K0-CCK'=S0-K0-CCK'-CS12
  hb1773 = mvD3.general-rewrite 50 auto

  hb1774 : Goal L.ax-CS12-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CS12
  hb1774 = mvD3.general-rewrite 50 auto

  hb1775 : Goal L.ax-CS12-S0-CK10-CCK'=S0-CK10-CCK'-CS12
  hb1775 = mvD3.general-rewrite 50 auto

  hb1776 : Goal L.ax-CS12-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CS12
  hb1776 = mvD3.general-rewrite 50 auto

  hb1777 : Goal L.ax-CS12-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CS12
  hb1777 = mvD3.general-rewrite 50 auto

  hb1778 : Goal L.ax-CS12-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CS12
  hb1778 = mvD3.general-rewrite 50 auto

  hb1779 : Goal L.ax-CS12-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CS12
  hb1779 = mvD3.general-rewrite 50 auto

  hb1780 : Goal L.ax-CS12-S0-CK20-CK10=S0-CK20-CK10-CS12
  hb1780 = mvD3.general-rewrite 50 auto

  hb1781 : Goal L.ax-CS12-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CS12
  hb1781 = mvD3.general-rewrite 50 auto

  hb1782 : Goal L.ax-CS12-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CS12
  hb1782 = mvD3.general-rewrite 50 auto

  hb1783 : Goal L.ax-CS12-S0-CK20-CCK'=S0-CK20-CCK'-CS12
  hb1783 = mvD3.general-rewrite 50 auto

  hb1784 : Goal L.ax-CS12-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CS12
  hb1784 = mvD3.general-rewrite 50 auto

  hb1785 : Goal L.ax-CS12-K0-S0-CK10=K0-S0-CK10-CS12
  hb1785 = mvD3.general-rewrite 50 auto

  hb1786 : Goal L.ax-CS12-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CS12
  hb1786 = mvD3.general-rewrite 50 auto

  hb1787 : Goal L.ax-CS12-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CS12
  hb1787 = mvD3.general-rewrite 50 auto

  hb1788 : Goal L.ax-CS12-K0-S0-CK20=K0-S0-CK20-CS12
  hb1788 = mvD3.general-rewrite 50 auto

  hb1789 : Goal L.ax-CS12-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CS12
  hb1789 = mvD3.general-rewrite 50 auto

  hb1790 : Goal L.ax-CS12-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CS12
  hb1790 = mvD3.general-rewrite 50 auto

  hb1791 : Goal L.ax-CS12-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CS12
  hb1791 = mvD3.general-rewrite 50 auto

  hb1792 : Goal L.ax-CS12-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CS12
  hb1792 = mvD3.general-rewrite 50 auto

  hb1793 : Goal L.ax-CS12-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CS12
  hb1793 = mvD3.general-rewrite 50 auto

  hb1794 : Goal L.ax-CS12-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CS12
  hb1794 = mvD3.general-rewrite 50 auto

  hb1795 : Goal L.ax-CS12-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CS12
  hb1795 = mvD3.general-rewrite 50 auto

  hb1796 : Goal L.ax-CS12-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CS12
  hb1796 = mvD3.general-rewrite 50 auto

  hb1797 : Goal L.ax-CS12-K0-CK10=K0-CK10-CS12
  hb1797 = mvD3.general-rewrite 50 auto

  hb1798 : Goal L.ax-CS12-K0-CK10-CCK'=K0-CK10-CCK'-CS12
  hb1798 = mvD3.general-rewrite 50 auto

  hb1799 : Goal L.ax-CS12-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CS12
  hb1799 = mvD3.general-rewrite 50 auto

  hb1800 : Goal L.ax-CS12-K0-CK20=K0-CK20-CS12
  hb1800 = mvD3.general-rewrite 50 auto

  hb1801 : Goal L.ax-CS12-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CS12
  hb1801 = mvD3.general-rewrite 50 auto

  hb1802 : Goal L.ax-CS12-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CS12
  hb1802 = mvD3.general-rewrite 50 auto

  hb1803 : Goal L.ax-CS12-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CS12
  hb1803 = mvD3.general-rewrite 50 auto

  hb1804 : Goal L.ax-CS12-K0-CK20-CK10=K0-CK20-CK10-CS12
  hb1804 = mvD3.general-rewrite 50 auto

  hb1805 : Goal L.ax-CS12-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CS12
  hb1805 = mvD3.general-rewrite 50 auto

  hb1806 : Goal L.ax-CS12-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CS12
  hb1806 = mvD3.general-rewrite 50 auto

  hb1807 : Goal L.ax-CS12-K0-CK20-CCK'=K0-CK20-CCK'-CS12
  hb1807 = mvD3.general-rewrite 50 auto

  hb1808 : Goal L.ax-CS12-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CS12
  hb1808 = mvD3.general-rewrite 50 auto

  hb1809 : Goal L.ax-CS12-K0-CCK'=K0-CCK'-CS12
  hb1809 = mvD3.general-rewrite 50 auto

  hb1810 : Goal L.ax-CS12-K0-CCK'-CCK'=K0-CCK'-CCK'-CS12
  hb1810 = mvD3.general-rewrite 50 auto

  hb1811 : Goal L.ax-CS12-CK10-CCK'=CK10-CCK'-CS12
  hb1811 = mvD3.general-rewrite 50 auto

  hb1812 : Goal L.ax-CS12-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CS12
  hb1812 = mvD3.general-rewrite 50 auto

  hb1813 : Goal L.ax-CS12-CK20-S0-CK10=CK20-S0-CK10-CS12
  hb1813 = mvD3.general-rewrite 50 auto

  hb1814 : Goal L.ax-CS12-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CS12
  hb1814 = mvD3.general-rewrite 50 auto

  hb1815 : Goal L.ax-CS12-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CS12
  hb1815 = mvD3.general-rewrite 50 auto

  hb1816 : Goal L.ax-CS12-CK20-CK10=CK20-CK10-CS12
  hb1816 = mvD3.general-rewrite 50 auto

  hb1817 : Goal L.ax-CS12-CK20-CK10-CCK'=CK20-CK10-CCK'-CS12
  hb1817 = mvD3.general-rewrite 50 auto

  hb1818 : Goal L.ax-CS12-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CS12
  hb1818 = mvD3.general-rewrite 50 auto

  hb1819 : Goal L.ax-CS12-CK20-CCK'=CK20-CCK'-CS12
  hb1819 = mvD3.general-rewrite 50 auto

  hb1820 : Goal L.ax-CS12-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CS12
  hb1820 = mvD3.general-rewrite 50 auto

  hb1821 : Goal L.ax-CCZ-S0-K0-S0-CK10=S0-K0-S0-CK10-CCX0-CS12-CCZ
  hb1821 = ListNF.listnfeq' nf-e4 auto

  hb1822 : Goal L.ax-CCZ-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCX0
  hb1822 = ListNF.listnfeq' nf-e4 auto

  hb1823 : Goal L.ax-CCZ-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCZ
  hb1823 = ListNF.listnfeq' nf-e4 auto

  hb1824 : Goal L.ax-CCZ-S0-K0-S0-CK20=S0-K0-S0-CK20-CCX0-CS12-CCZ
  hb1824 = ListNF.listnfeq' nf-e4 auto

  hb1825 : Goal L.ax-CCZ-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCZ
  hb1825 = ListNF.listnfeq' nf-e4 auto

  hb1826 : Goal L.ax-CCZ-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCX0-CS12-CCZ
  hb1826 = ListNF.listnfeq' nf-e4 auto

  hb1827 : Goal L.ax-CCZ-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CCX0
  hb1827 = ListNF.listnfeq' nf-e4 auto

  hb1828 : Goal L.ax-CCZ-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCX0-CS12-CS12-CS12-CCZ
  hb1828 = ListNF.listnfeq' nf-e4 auto

  hb1829 : Goal L.ax-CCZ-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCX0-CS12-CS12
  hb1829 = ListNF.listnfeq' nf-e4 auto

  hb1830 : Goal L.ax-CCZ-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CS12-CS12-CCZ
  hb1830 = ListNF.listnfeq' nf-e4 auto

  hb1831 : Goal L.ax-CCZ-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCX0
  hb1831 = ListNF.listnfeq' nf-e4 auto

  hb1832 : Goal L.ax-CCZ-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCZ
  hb1832 = ListNF.listnfeq' nf-e4 auto

  hb1833 : Goal L.ax-CCZ-S0-K0-CK10=S0-K0-CK10-CCZ
  hb1833 = ListNF.listnfeq' nf-e4 auto

  hb1834 : Goal L.ax-CCZ-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CCX0-CS12-CCZ
  hb1834 = ListNF.listnfeq' nf-e4 auto

  hb1835 : Goal L.ax-CCZ-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CCX0
  hb1835 = ListNF.listnfeq' nf-e4 auto

  hb1836 : Goal L.ax-CCZ-S0-K0-CK20=S0-K0-CK20-CCZ
  hb1836 = ListNF.listnfeq' nf-e4 auto

  hb1837 : Goal L.ax-CCZ-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CCX0
  hb1837 = ListNF.listnfeq' nf-e4 auto

  hb1838 : Goal L.ax-CCZ-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCZ
  hb1838 = ListNF.listnfeq' nf-e4 auto

  hb1839 : Goal L.ax-CCZ-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ
  hb1839 = ListNF.listnfeq' nf-e4 auto

  hb1840 : Goal L.ax-CCZ-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCX0
  hb1840 = ListNF.listnfeq' nf-e4 auto

  hb1841 : Goal L.ax-CCZ-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCZ
  hb1841 = ListNF.listnfeq' nf-e4 auto

  hb1842 : Goal L.ax-CCZ-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CCX0-CS12-CCZ
  hb1842 = ListNF.listnfeq' nf-e4 auto

  hb1843 : Goal L.ax-CCZ-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CCX0-CS12-CCZ
  hb1843 = ListNF.listnfeq' nf-e4 auto

  hb1844 : Goal L.ax-CCZ-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CCX0
  hb1844 = ListNF.listnfeq' nf-e4 auto

  hb1845 : Goal L.ax-CCZ-S0-K0-CCK'=S0-K0-CCK'-CCZ
  hb1845 = ListNF.listnfeq' nf-e4 auto

  hb1846 : Goal L.ax-CCZ-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CCX0-CS12-CCZ
  hb1846 = ListNF.listnfeq' nf-e4 auto

  hb1847 : Goal L.ax-CCZ-S0-CK10-CCK'=S0-CK10-CCK'-CCZ
  hb1847 = ListNF.listnfeq' nf-e3 auto

  hb1848 : Goal L.ax-CCZ-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ
  hb1848 = ListNF.listnfeq' nf-e3 auto

  hb1849 : Goal L.ax-CCZ-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CCX0-CS12-CCZ
  hb1849 = ListNF.listnfeq' nf-e3 auto

  hb1850 : Goal L.ax-CCZ-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CCX0
  hb1850 = ListNF.listnfeq' nf-e3 auto

  hb1851 : Goal L.ax-CCZ-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CCZ
  hb1851 = ListNF.listnfeq' nf-e3 auto

  hb1852 : Goal L.ax-CCZ-S0-CK20-CK10=S0-CK20-CK10-CCZ
  hb1852 = ListNF.listnfeq' nf-e3 auto

  hb1853 : Goal L.ax-CCZ-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CCX0-CS12-CCZ
  hb1853 = ListNF.listnfeq' nf-e3 auto

  hb1854 : Goal L.ax-CCZ-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CCX0
  hb1854 = ListNF.listnfeq' nf-e3 auto

  hb1855 : Goal L.ax-CCZ-S0-CK20-CCK'=S0-CK20-CCK'-CCZ
  hb1855 = ListNF.listnfeq' nf-e3 auto

  hb1856 : Goal L.ax-CCZ-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CCX0-CS12-CCZ
  hb1856 = ListNF.listnfeq' nf-e3 auto

  hb1857 : Goal L.ax-CCZ-K0-S0-CK10=K0-S0-CK10-CCX0-CS12-CCZ
  hb1857 = ListNF.listnfeq' nf-e4 auto

  hb1858 : Goal L.ax-CCZ-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CCX0
  hb1858 = ListNF.listnfeq' nf-e4 auto

  hb1859 : Goal L.ax-CCZ-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CCZ
  hb1859 = ListNF.listnfeq' nf-e4 auto

  hb1860 : Goal L.ax-CCZ-K0-S0-CK20=K0-S0-CK20-CCX0-CS12-CCZ
  hb1860 = ListNF.listnfeq' nf-e4 auto

  hb1861 : Goal L.ax-CCZ-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCZ
  hb1861 = ListNF.listnfeq' nf-e4 auto

  hb1862 : Goal L.ax-CCZ-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCX0-CS12-CCZ
  hb1862 = ListNF.listnfeq' nf-e4 auto

  hb1863 : Goal L.ax-CCZ-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CCX0
  hb1863 = ListNF.listnfeq' nf-e4 auto

  hb1864 : Goal L.ax-CCZ-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCX0-CS12-CS12-CS12-CCZ
  hb1864 = ListNF.listnfeq' nf-e4 auto

  hb1865 : Goal L.ax-CCZ-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CCX0-CS12-CS12
  hb1865 = ListNF.listnfeq' nf-e4 auto

  hb1866 : Goal L.ax-CCZ-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CS12-CS12-CCZ
  hb1866 = ListNF.listnfeq' nf-e4 auto

  hb1867 : Goal L.ax-CCZ-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CCX0
  hb1867 = ListNF.listnfeq' nf-e4 auto

  hb1868 : Goal L.ax-CCZ-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CCZ
  hb1868 = ListNF.listnfeq' nf-e4 auto

  hb1869 : Goal L.ax-CCZ-K0-CK10=K0-CK10-CCZ
  hb1869 = ListNF.listnfeq' nf-e4 auto

  hb1870 : Goal L.ax-CCZ-K0-CK10-CCK'=K0-CK10-CCK'-CCX0-CS12-CCZ
  hb1870 = ListNF.listnfeq' nf-e4 auto

  hb1871 : Goal L.ax-CCZ-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CCX0
  hb1871 = ListNF.listnfeq' nf-e4 auto

  hb1872 : Goal L.ax-CCZ-K0-CK20=K0-CK20-CCZ
  hb1872 = ListNF.listnfeq' nf-e4 auto

  hb1873 : Goal L.ax-CCZ-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CCX0
  hb1873 = ListNF.listnfeq' nf-e4 auto

  hb1874 : Goal L.ax-CCZ-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CCZ
  hb1874 = ListNF.listnfeq' nf-e4 auto

  hb1875 : Goal L.ax-CCZ-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ
  hb1875 = ListNF.listnfeq' nf-e4 auto


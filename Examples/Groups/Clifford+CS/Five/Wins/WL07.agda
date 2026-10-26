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

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wl1312 : Base 4 → ⟪ (ℓ "专些") ⟫ʷ ≈ ⟪ (ℓ "些专") ⟫ʷ
wl1312 c4 = lw4 c4 (ℓ "专些") (ℓ "些专") tt tt Eq.refl

wl1313 : Base 4 → ⟪ (ℓ "丒乩乙乪乙乇专") ⟫ʷ ≈ ⟪ (ℓ "亩") ⟫ʷ
wl1313 c4 = lw0 c4 (ℓ "丒乩乙乪乙乇专") (ℓ "亩") tt tt Eq.refl

wl1314 : Base 4 → ⟪ (ℓ "京亩") ⟫ʷ ≈ ⟪ (ℓ "亩亰京") ⟫ʷ
wl1314 c4 = lw0 c4 (ℓ "京亩") (ℓ "亩亰京") tt tt Eq.refl

wl1315 : Base 4 → ⟪ (ℓ "亊亰亊丢") ⟫ʷ ≈ ⟪ (ℓ "亲") ⟫ʷ
wl1315 c4 = lw0 c4 (ℓ "亊亰亊丢") (ℓ "亲") tt tt Eq.refl

wl1316 : Base 4 → ⟪ (ℓ "亇亰亇丢") ⟫ʷ ≈ ⟪ (ℓ "亱") ⟫ʷ
wl1316 c4 = lw0 c4 (ℓ "亇亰亇丢") (ℓ "亱") tt tt Eq.refl

wl1317 : Base 4 → ⟪ (ℓ "亐乜交") ⟫ʷ ≈ ⟪ (ℓ "乜亐") ⟫ʷ
wl1317 c4 = lw4 c4 (ℓ "亐乜交") (ℓ "乜亐") tt tt Eq.refl

wl1318 : Base 4 → ⟪ (ℓ "乜交交") ⟫ʷ ≈ ⟪ (ℓ "乜") ⟫ʷ
wl1318 c4 = lw4 c4 (ℓ "乜交交") (ℓ "乜") tt tt Eq.refl

wl1319 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "亰亳乗亳亰乗") ⟫ʷ
wl1319 c4 = lw0 c4 (ℓ "交") (ℓ "亰亳乗亳亰乗") tt tt Eq.refl

wl1320 : Base 4 → ⟪ (ℓ "交为二") ⟫ʷ ≈ ⟪ (ℓ "为交") ⟫ʷ
wl1320 c4 = lw4 c4 (ℓ "交为二") (ℓ "为交") tt tt Eq.refl

wl1321 : Base 4 → ⟪ (ℓ "交丩") ⟫ʷ ≈ ⟪ (ℓ "丩交") ⟫ʷ
wl1321 c4 = lw4 c4 (ℓ "交丩") (ℓ "丩交") tt tt Eq.refl

wl1322 : Base 4 → ⟪ (ℓ "为二二") ⟫ʷ ≈ ⟪ (ℓ "为") ⟫ʷ
wl1322 c4 = lw4 c4 (ℓ "为二二") (ℓ "为") tt tt Eq.refl

wl1323 : Base 4 → ⟪ (ℓ "交亱京") ⟫ʷ ≈ ⟪ (ℓ "亱交") ⟫ʷ
wl1323 c4 = lw0 c4 (ℓ "交亱京") (ℓ "亱交") tt tt Eq.refl

wl1324 : Base 4 → ⟪ (ℓ "交买") ⟫ʷ ≈ ⟪ (ℓ "买交") ⟫ʷ
wl1324 c4 = lw4 c4 (ℓ "交买") (ℓ "买交") tt tt Eq.refl

wl1325 : Base 4 → ⟪ (ℓ "交丳亐") ⟫ʷ ≈ ⟪ (ℓ "丳交") ⟫ʷ
wl1325 c4 = lw4 c4 (ℓ "交丳亐") (ℓ "丳交") tt tt Eq.refl

wl1326 : Base 4 → ⟪ (ℓ "丳亐亐") ⟫ʷ ≈ ⟪ (ℓ "丳") ⟫ʷ
wl1326 c4 = lw4 c4 (ℓ "丳亐亐") (ℓ "丳") tt tt Eq.refl

wl1327 : Base 4 → ⟪ (ℓ "交亲亨") ⟫ʷ ≈ ⟪ (ℓ "亲交") ⟫ʷ
wl1327 c4 = lw0 c4 (ℓ "交亲亨") (ℓ "亲交") tt tt Eq.refl

wl1328 : Base 4 → ⟪ (ℓ "交亏") ⟫ʷ ≈ ⟪ (ℓ "亏交亐") ⟫ʷ
wl1328 c4 = lw4 c4 (ℓ "交亏") (ℓ "亏交亐") tt tt Eq.refl

wl1329 : Base 4 → ⟪ (ℓ "丶亏") ⟫ʷ ≈ ⟪ (ℓ "亏丶") ⟫ʷ
wl1329 c4 = lw4 c4 (ℓ "丶亏") (ℓ "亏丶") tt tt Eq.refl

wl1330 : Base 4 → ⟪ (ℓ "交二亓") ⟫ʷ ≈ ⟪ (ℓ "亓交") ⟫ʷ
wl1330 c4 = lw4 c4 (ℓ "交二亓") (ℓ "亓交") tt tt Eq.refl

wl1331 : Base 4 → ⟪ (ℓ "丙亓") ⟫ʷ ≈ ⟪ (ℓ "亓丙") ⟫ʷ
wl1331 c4 = lw4 c4 (ℓ "丙亓") (ℓ "亓丙") tt tt Eq.refl

wl1332 : Base 4 → ⟪ (ℓ "乕亱") ⟫ʷ ≈ ⟪ (ℓ "亱乕") ⟫ʷ
wl1332 c4 = lw0 c4 (ℓ "乕亱") (ℓ "亱乕") tt tt Eq.refl

wl1333 : Base 4 → ⟪ (ℓ "交京亱") ⟫ʷ ≈ ⟪ (ℓ "亱交") ⟫ʷ
wl1333 c4 = lw0 c4 (ℓ "交京亱") (ℓ "亱交") tt tt Eq.refl

wl1334 : Base 4 → ⟪ (ℓ "交京") ⟫ʷ ≈ ⟪ (ℓ "亱交亱") ⟫ʷ
wl1334 c4 = lw0 c4 (ℓ "交京") (ℓ "亱交亱") tt tt Eq.refl

wl1335 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "京交京") ⟫ʷ
wl1335 c4 = lw0 c4 (ℓ "交") (ℓ "京交京") tt tt Eq.refl

wl1336 : Base 4 → ⟪ (ℓ "亨亦") ⟫ʷ ≈ ⟪ (ℓ "亦亨京") ⟫ʷ
wl1336 c4 = lw0 c4 (ℓ "亨亦") (ℓ "亦亨京") tt tt Eq.refl

wl1337 : Base 4 → ⟪ (ℓ "丬亦") ⟫ʷ ≈ ⟪ (ℓ "亦丬亚") ⟫ʷ
wl1337 c4 = lw4 c4 (ℓ "丬亦") (ℓ "亦丬亚") tt tt Eq.refl

wl1338 : Base 4 → ⟪ (ℓ "亚亦") ⟫ʷ ≈ ⟪ (ℓ "亦亚") ⟫ʷ
wl1338 c4 = lw4 c4 (ℓ "亚亦") (ℓ "亦亚") tt tt Eq.refl

wl1339 : Base 4 → ⟪ (ℓ "丬亚亚") ⟫ʷ ≈ ⟪ (ℓ "丬") ⟫ʷ
wl1339 c4 = lw4 c4 (ℓ "丬亚亚") (ℓ "丬") tt tt Eq.refl

wl1340 : Base 4 → ⟪ (ℓ "丫些") ⟫ʷ ≈ ⟪ (ℓ "产丫") ⟫ʷ
wl1340 c4 = lw4 c4 (ℓ "丫些") (ℓ "产丫") tt tt Eq.refl

wl1341 : Base 4 → ⟪ (ℓ "交产乻产交乻") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
wl1341 c4 = lw0 c4 (ℓ "交产乻产交乻") (ℓ "亨") tt tt Eq.refl

wl1342 : Base 4 → ⟪ (ℓ "亰亪") ⟫ʷ ≈ ⟪ (ℓ "亪京亰") ⟫ʷ
wl1342 c4 = lw0 c4 (ℓ "亰亪") (ℓ "亪京亰") tt tt Eq.refl

wl1343 : Base 4 → ⟪ (ℓ "亘乳") ⟫ʷ ≈ ⟪ (ℓ "乳亘") ⟫ʷ
wl1343 c4 = lw4 c4 (ℓ "亘乳") (ℓ "乳亘") tt tt Eq.refl

wl1344 : Base 4 → ⟪ (ℓ "京亰亪") ⟫ʷ ≈ ⟪ (ℓ "亪亰") ⟫ʷ
wl1344 c4 = lw0 c4 (ℓ "京亰亪") (ℓ "亪亰") tt tt Eq.refl

wl1345 : Base 4 → ⟪ (ℓ "亘亓二") ⟫ʷ ≈ ⟪ (ℓ "亓亘") ⟫ʷ
wl1345 c4 = lw4 c4 (ℓ "亘亓二") (ℓ "亓亘") tt tt Eq.refl

wl1346 : Base 4 → ⟪ (ℓ "丞丨买丩买乎丟") ⟫ʷ ≈ ⟪ (ℓ "亓") ⟫ʷ
wl1346 c4 = lw4 c4 (ℓ "丞丨买丩买乎丟") (ℓ "亓") tt tt Eq.refl

wl1347 : Base 4 → ⟪ (ℓ "亓二二") ⟫ʷ ≈ ⟪ (ℓ "亓") ⟫ʷ
wl1347 c4 = lw4 c4 (ℓ "亓二二") (ℓ "亓") tt tt Eq.refl

wl1348 : Base 4 → ⟪ (ℓ "丬亚") ⟫ʷ ≈ ⟪ (ℓ "亚丬") ⟫ʷ
wl1348 c4 = lw4 c4 (ℓ "丬亚") (ℓ "亚丬") tt tt Eq.refl

wl1349 : Base 4 → ⟪ (ℓ "乄亚") ⟫ʷ ≈ ⟪ (ℓ "亚乄亦") ⟫ʷ
wl1349 c4 = lw4 c4 (ℓ "乄亚") (ℓ "亚乄亦") tt tt Eq.refl

wl1350 : Base 4 → ⟪ (ℓ "亨亦京") ⟫ʷ ≈ ⟪ (ℓ "亦亨") ⟫ʷ
wl1350 c4 = lw0 c4 (ℓ "亨亦京") (ℓ "亦亨") tt tt Eq.refl

wl1351 : Base 4 → ⟪ (ℓ "乳亚") ⟫ʷ ≈ ⟪ (ℓ "亚乳") ⟫ʷ
wl1351 c4 = lw4 c4 (ℓ "乳亚") (ℓ "亚乳") tt tt Eq.refl

wl1352 : Base 4 → ⟪ (ℓ "乄亦亦") ⟫ʷ ≈ ⟪ (ℓ "乄") ⟫ʷ
wl1352 c4 = lw4 c4 (ℓ "乄亦亦") (ℓ "乄") tt tt Eq.refl

wl1353 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "丨买丩买乎") ⟫ʷ
wl1353 c4 = lw4 c4 (ℓ "亐") (ℓ "丨买丩买乎") tt tt Eq.refl

wl1354 : Base 4 → ⟪ (ℓ "交亐亏") ⟫ʷ ≈ ⟪ (ℓ "亏交") ⟫ʷ
wl1354 c4 = lw4 c4 (ℓ "交亐亏") (ℓ "亏交") tt tt Eq.refl

wl1355 : Base 4 → ⟪ (ℓ "交亨") ⟫ʷ ≈ ⟪ (ℓ "亲交亲") ⟫ʷ
wl1355 c4 = lw0 c4 (ℓ "交亨") (ℓ "亲交亲") tt tt Eq.refl

wl1356 : Base 4 → ⟪ (ℓ "京产") ⟫ʷ ≈ ⟪ (ℓ "产京亨") ⟫ʷ
wl1356 c4 = lw0 c4 (ℓ "京产") (ℓ "产京亨") tt tt Eq.refl

wl1357 : Base 4 → ⟪ (ℓ "丬产") ⟫ʷ ≈ ⟪ (ℓ "产丬些") ⟫ʷ
wl1357 c4 = lw4 c4 (ℓ "丬产") (ℓ "产丬些") tt tt Eq.refl

wl1358 : Base 4 → ⟪ (ℓ "些产") ⟫ʷ ≈ ⟪ (ℓ "产些") ⟫ʷ
wl1358 c4 = lw4 c4 (ℓ "些产") (ℓ "产些") tt tt Eq.refl

wl1359 : Base 4 → ⟪ (ℓ "丬些些") ⟫ʷ ≈ ⟪ (ℓ "丬") ⟫ʷ
wl1359 c4 = lw4 c4 (ℓ "丬些些") (ℓ "丬") tt tt Eq.refl

wl1360 : Base 4 → ⟪ (ℓ "亰亮") ⟫ʷ ≈ ⟪ (ℓ "亮亨亰") ⟫ʷ
wl1360 c4 = lw0 c4 (ℓ "亰亮") (ℓ "亮亨亰") tt tt Eq.refl

wl1361 : Base 4 → ⟪ (ℓ "亨亰亮") ⟫ʷ ≈ ⟪ (ℓ "亮亰") ⟫ʷ
wl1361 c4 = lw0 c4 (ℓ "亨亰亮") (ℓ "亮亰") tt tt Eq.refl

wl1362 : Base 4 → ⟪ (ℓ "亘亏亐") ⟫ʷ ≈ ⟪ (ℓ "亏亘") ⟫ʷ
wl1362 c4 = lw4 c4 (ℓ "亘亏亐") (ℓ "亏亘") tt tt Eq.refl

wl1363 : Base 4 → ⟪ (ℓ "丘丨乜丩乜乇丙") ⟫ʷ ≈ ⟪ (ℓ "亏") ⟫ʷ
wl1363 c4 = lw4 c4 (ℓ "丘丨乜丩乜乇丙") (ℓ "亏") tt tt Eq.refl

wl1364 : Base 4 → ⟪ (ℓ "丙亮") ⟫ʷ ≈ ⟪ (ℓ "亮丙") ⟫ʷ
wl1364 c4 = lw0 c4 (ℓ "丙亮") (ℓ "亮丙") tt tt Eq.refl

wl1365 : Base 4 → ⟪ (ℓ "丘亮") ⟫ʷ ≈ ⟪ (ℓ "亮丘") ⟫ʷ
wl1365 c4 = lw0 c4 (ℓ "丘亮") (ℓ "亮丘") tt tt Eq.refl

wl1366 : Base 4 → ⟪ (ℓ "亏亐亐") ⟫ʷ ≈ ⟪ (ℓ "亏") ⟫ʷ
wl1366 c4 = lw4 c4 (ℓ "亏亐亐") (ℓ "亏") tt tt Eq.refl

wl1367 : Base 4 → ⟪ (ℓ "乄些") ⟫ʷ ≈ ⟪ (ℓ "些乄产") ⟫ʷ
wl1367 c4 = lw4 c4 (ℓ "乄些") (ℓ "些乄产") tt tt Eq.refl

wl1368 : Base 4 → ⟪ (ℓ "京产亨") ⟫ʷ ≈ ⟪ (ℓ "产京") ⟫ʷ
wl1368 c4 = lw0 c4 (ℓ "京产亨") (ℓ "产京") tt tt Eq.refl

wl1369 : Base 4 → ⟪ (ℓ "乄产产") ⟫ʷ ≈ ⟪ (ℓ "乄") ⟫ʷ
wl1369 c4 = lw4 c4 (ℓ "乄产产") (ℓ "乄") tt tt Eq.refl

wl1370 : Base 4 → ⟪ (ℓ "亐亓个") ⟫ʷ ≈ ⟪ (ℓ "亓亐") ⟫ʷ
wl1370 c4 = lw4 c4 (ℓ "亐亓个") (ℓ "亓亐") tt tt Eq.refl

wl1371 : Base 4 → ⟪ (ℓ "乪亮") ⟫ʷ ≈ ⟪ (ℓ "亮乪") ⟫ʷ
wl1371 c4 = lw0 c4 (ℓ "乪亮") (ℓ "亮乪") tt tt Eq.refl

wl1372 : Base 4 → ⟪ (ℓ "亱亱") ⟫ʷ ≈ ⟪ (ℓ "亲亱亲亲亱亲") ⟫ʷ
wl1372 c4 = lw0 c4 (ℓ "亱亱") (ℓ "亲亱亲亲亱亲") tt tt Eq.refl

wl1373 : Base 4 → ⟪ (ℓ "亲亱亲亲亱亲") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1373 c4 = lw0 c4 (ℓ "亲亱亲亲亱亲") [] tt tt Eq.refl

wl1374 : Base 4 → ⟪ (ℓ "丘乹书乺书乩丙") ⟫ʷ ≈ ⟪ (ℓ "亱") ⟫ʷ
wl1374 c4 = lw0 c4 (ℓ "丘乹书乺书乩丙") (ℓ "亱") tt tt Eq.refl

wl1375 : Base 4 → ⟪ (ℓ "丙云") ⟫ʷ ≈ ⟪ (ℓ "云丙") ⟫ʷ
wl1375 c4 = lw4 c4 (ℓ "丙云") (ℓ "云丙") tt tt Eq.refl

wl1376 : Base 4 → ⟪ (ℓ "丘乹乭乺乭乢丙") ⟫ʷ ≈ ⟪ (ℓ "亱") ⟫ʷ
wl1376 c4 = lw0 c4 (ℓ "丘乹乭乺乭乢丙") (ℓ "亱") tt tt Eq.refl

wl1377 : Base 4 → ⟪ (ℓ "京亰亰亰亭乇亰亰亭么亪") ⟫ʷ ≈ ⟪ (ℓ "亰亰亰亭乇亰亰亭么亪京") ⟫ʷ
wl1377 c4 = lw0 c4 (ℓ "京亰亰亰亭乇亰亰亭么亪") (ℓ "亰亰亰亭乇亰亰亭么亪京") tt tt Eq.refl

wl1378 : Base 4 → ⟪ (ℓ "亭乇亭么亪亭乇亰亭么亪京亲亱亲亲乎亲乏亲亨亱京亲亨") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1378 c4 = lw0 c4 (ℓ "亭乇亭么亪亭乇亰亭么亪京亲亱亲亲乎亲乏亲亨亱京亲亨") [] tt tt Eq.refl

wl1379 : Base 4 → ⟪ (ℓ "京亭义亭京义") ⟫ʷ ≈ ⟪ (ℓ "亰") ⟫ʷ
wl1379 c4 = lw0 c4 (ℓ "京亭义亭京义") (ℓ "亰") tt tt Eq.refl

wl1380 : Base 4 → ⟪ (ℓ "丞丨乳丩乳丶丟") ⟫ʷ ≈ ⟪ (ℓ "亓") ⟫ʷ
wl1380 c4 = lw4 c4 (ℓ "丞丨乳丩乳丶丟") (ℓ "亓") tt tt Eq.refl

wl1381 : Base 4 → ⟪ (ℓ "亏亓产") ⟫ʷ ≈ ⟪ (ℓ "产亏") ⟫ʷ
wl1381 c4 = lw4 c4 (ℓ "亏亓产") (ℓ "产亏") tt tt Eq.refl

wl1382 : Base 4 → ⟪ (ℓ "亰亨产") ⟫ʷ ≈ ⟪ (ℓ "产亰") ⟫ʷ
wl1382 c4 = lw0 c4 (ℓ "亰亨产") (ℓ "产亰") tt tt Eq.refl

wl1383 : Base 4 → ⟪ (ℓ "亰亨") ⟫ʷ ≈ ⟪ (ℓ "产亰产") ⟫ʷ
wl1383 c4 = lw0 c4 (ℓ "亰亨") (ℓ "产亰产") tt tt Eq.refl

wl1384 : Base 4 → ⟪ (ℓ "乇亓") ⟫ʷ ≈ ⟪ (ℓ "亓乇") ⟫ʷ
wl1384 c4 = lw4 c4 (ℓ "乇亓") (ℓ "亓乇") tt tt Eq.refl

wl1385 : Base 4 → ⟪ (ℓ "亨亰亨") ⟫ʷ ≈ ⟪ (ℓ "亰") ⟫ʷ
wl1385 c4 = lw0 c4 (ℓ "亨亰亨") (ℓ "亰") tt tt Eq.refl

wl1386 : Base 4 → ⟪ (ℓ "亏亓") ⟫ʷ ≈ ⟪ (ℓ "亓亏") ⟫ʷ
wl1386 c4 = lw4 c4 (ℓ "亏亓") (ℓ "亓亏") tt tt Eq.refl

wl1387 : Base 4 → ⟪ (ℓ "丘丨也丩也丯丙") ⟫ʷ ≈ ⟪ (ℓ "亏") ⟫ʷ
wl1387 c4 = lw4 c4 (ℓ "丘丨也丩也丯丙") (ℓ "亏") tt tt Eq.refl

wl1388 : Base 4 → ⟪ (ℓ "亰乒亨") ⟫ʷ ≈ ⟪ (ℓ "乒亰") ⟫ʷ
wl1388 c4 = lw0 c4 (ℓ "亰乒亨") (ℓ "乒亰") tt tt Eq.refl

wl1389 : Base 4 → ⟪ (ℓ "乒亨亨") ⟫ʷ ≈ ⟪ (ℓ "乒") ⟫ʷ
wl1389 c4 = lw0 c4 (ℓ "乒亨亨") (ℓ "乒") tt tt Eq.refl

wl1390 : Base 4 → ⟪ (ℓ "乳亏") ⟫ʷ ≈ ⟪ (ℓ "亏乳亚") ⟫ʷ
wl1390 c4 = lw4 c4 (ℓ "乳亏") (ℓ "亏乳亚") tt tt Eq.refl

wl1391 : Base 4 → ⟪ (ℓ "亏亚") ⟫ʷ ≈ ⟪ (ℓ "亚亏") ⟫ʷ
wl1391 c4 = lw4 c4 (ℓ "亏亚") (ℓ "亚亏") tt tt Eq.refl

wl1392 : Base 4 → ⟪ (ℓ "乳亚亚") ⟫ʷ ≈ ⟪ (ℓ "乳") ⟫ʷ
wl1392 c4 = lw4 c4 (ℓ "乳亚亚") (ℓ "乳") tt tt Eq.refl

wl1393 : Base 4 → ⟪ (ℓ "亘乒二") ⟫ʷ ≈ ⟪ (ℓ "乒亘") ⟫ʷ
wl1393 c4 = lw4 c4 (ℓ "亘乒二") (ℓ "乒亘") tt tt Eq.refl

wl1394 : Base 4 → ⟪ (ℓ "乒二二") ⟫ʷ ≈ ⟪ (ℓ "乒") ⟫ʷ
wl1394 c4 = lw4 c4 (ℓ "乒二二") (ℓ "乒") tt tt Eq.refl

wl1395 : Base 4 → ⟪ (ℓ "亘二产") ⟫ʷ ≈ ⟪ (ℓ "产亘") ⟫ʷ
wl1395 c4 = lw4 c4 (ℓ "亘二产") (ℓ "产亘") tt tt Eq.refl

wl1396 : Base 4 → ⟪ (ℓ "亰亮") ⟫ʷ ≈ ⟪ (ℓ "亮亰亨") ⟫ʷ
wl1396 c4 = lw0 c4 (ℓ "亰亮") (ℓ "亮亰亨") tt tt Eq.refl

wl1397 : Base 4 → ⟪ (ℓ "丞乕乽乖乽乎丟") ⟫ʷ ≈ ⟪ (ℓ "亮") ⟫ʷ
wl1397 c4 = lw0 c4 (ℓ "丞乕乽乖乽乎丟") (ℓ "亮") tt tt Eq.refl

wl1398 : Base 4 → ⟪ (ℓ "亨乳亰") ⟫ʷ ≈ ⟪ (ℓ "乳亨") ⟫ʷ
wl1398 c4 = lw0 c4 (ℓ "亨乳亰") (ℓ "乳亨") tt tt Eq.refl

wl1399 : Base 4 → ⟪ (ℓ "亨乺") ⟫ʷ ≈ ⟪ (ℓ "乺亨") ⟫ʷ
wl1399 c4 = lw0 c4 (ℓ "亨乺") (ℓ "乺亨") tt tt Eq.refl

wl1400 : Base 4 → ⟪ (ℓ "乳亰亰") ⟫ʷ ≈ ⟪ (ℓ "乳") ⟫ʷ
wl1400 c4 = lw0 c4 (ℓ "乳亰亰") (ℓ "乳") tt tt Eq.refl

wl1401 : Base 4 → ⟪ (ℓ "乒亚") ⟫ʷ ≈ ⟪ (ℓ "亚乒亏") ⟫ʷ
wl1401 c4 = lw4 c4 (ℓ "乒亚") (ℓ "亚乒亏") tt tt Eq.refl

wl1402 : Base 4 → ⟪ (ℓ "乒亏亏") ⟫ʷ ≈ ⟪ (ℓ "乒") ⟫ʷ
wl1402 c4 = lw4 c4 (ℓ "乒亏亏") (ℓ "乒") tt tt Eq.refl

wl1403 : Base 4 → ⟪ (ℓ "交产义") ⟫ʷ ≈ ⟪ (ℓ "产交") ⟫ʷ
wl1403 c4 = lw4 c4 (ℓ "交产义") (ℓ "产交") tt tt Eq.refl

wl1404 : Base 4 → ⟪ (ℓ "乺亪") ⟫ʷ ≈ ⟪ (ℓ "亪乺") ⟫ʷ
wl1404 c4 = lw0 c4 (ℓ "乺亪") (ℓ "亪乺") tt tt Eq.refl

wl1405 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "亰京亰") ⟫ʷ
wl1405 c4 = lw0 c4 (ℓ "京") (ℓ "亰京亰") tt tt Eq.refl

wl1406 : Base 4 → ⟪ (ℓ "亨京亲") ⟫ʷ ≈ ⟪ (ℓ "亲京") ⟫ʷ
wl1406 c4 = lw0 c4 (ℓ "亨京亲") (ℓ "亲京") tt tt Eq.refl

wl1407 : Base 4 → ⟪ (ℓ "亍产亙") ⟫ʷ ≈ ⟪ (ℓ "亙产") ⟫ʷ
wl1407 c4 = lw4 c4 (ℓ "亍产亙") (ℓ "亙产") tt tt Eq.refl

wl1408 : Base 4 → ⟪ (ℓ "京亨") ⟫ʷ ≈ ⟪ (ℓ "产京产") ⟫ʷ
wl1408 c4 = lw0 c4 (ℓ "京亨") (ℓ "产京产") tt tt Eq.refl

wl1409 : Base 4 → ⟪ (ℓ "丘") ⟫ʷ ≈ ⟪ (ℓ "並亇並亇") ⟫ʷ
wl1409 c4 = lw0 c4 (ℓ "丘") (ℓ "並亇並亇") tt tt Eq.refl

wl1410 : Base 4 → ⟪ (ℓ "东") ⟫ʷ ≈ ⟪ (ℓ "並乹並乹") ⟫ʷ
wl1410 c4 = lw0 c4 (ℓ "东") (ℓ "並乹並乹") tt tt Eq.refl

wl1411 : Base 4 → ⟪ (ℓ "並丢並丢") ⟫ʷ ≈ ⟪ (ℓ "一") ⟫ʷ
wl1411 c4 = lw1 c4 (ℓ "並丢並丢") (ℓ "一") tt tt Eq.refl

wl1412 : Base 4 → ⟪ (ℓ "丐") ⟫ʷ ≈ ⟪ (ℓ "並乕並乕") ⟫ʷ
wl1412 c4 = lw0 c4 (ℓ "丐") (ℓ "並乕並乕") tt tt Eq.refl

wl1413 : Base 4 → ⟪ (ℓ "丞乩乶乪乶乹丟") ⟫ʷ ≈ ⟪ (ℓ "亲") ⟫ʷ
wl1413 c4 = lw0 c4 (ℓ "丞乩乶乪乶乹丟") (ℓ "亲") tt tt Eq.refl

wl1414 : Base 4 → ⟪ (ℓ "交乇交亨亲乎") ⟫ʷ ≈ ⟪ (ℓ "亲乎乇亨") ⟫ʷ
wl1414 c4 = lw0 c4 (ℓ "交乇交亨亲乎") (ℓ "亲乎乇亨") tt tt Eq.refl

wl1415 : Base 4 → ⟪ (ℓ "亨亲乎乇亨") ⟫ʷ ≈ ⟪ (ℓ "亲乎乇") ⟫ʷ
wl1415 c4 = lw0 c4 (ℓ "亨亲乎乇亨") (ℓ "亲乎乇") tt tt Eq.refl

wl1416 : Base 4 → ⟪ (ℓ "乇") ⟫ʷ ≈ ⟪ (ℓ "亲乎乇亨亲乏亲乎亲乏") ⟫ʷ
wl1416 c4 = lw0 c4 (ℓ "乇") (ℓ "亲乎乇亨亲乏亲乎亲乏") tt tt Eq.refl

wl1417 : Base 4 → ⟪ (ℓ "丒") ⟫ʷ ≈ ⟪ (ℓ "並亄並亄") ⟫ʷ
wl1417 c4 = lw0 c4 (ℓ "丒") (ℓ "並亄並亄") tt tt Eq.refl

wl1418 : Base 4 → ⟪ (ℓ "世") ⟫ʷ ≈ ⟪ (ℓ "並乩並乩") ⟫ʷ
wl1418 c4 = lw0 c4 (ℓ "世") (ℓ "並乩並乩") tt tt Eq.refl

wl1419 : Base 4 → ⟪ (ℓ "丞") ⟫ʷ ≈ ⟪ (ℓ "並亊並亊") ⟫ʷ
wl1419 c4 = lw0 c4 (ℓ "丞") (ℓ "並亊並亊") tt tt Eq.refl

wl1420 : Base 4 → ⟪ (ℓ "丌上上丌一") ⟫ʷ ≈ ⟪ (ℓ "与") ⟫ʷ
wl1420 c4 = lw4 c4 (ℓ "丌上上丌一") (ℓ "与") tt tt Eq.refl

wl1421 : Base 4 → ⟪ (ℓ "亦亏亓") ⟫ʷ ≈ ⟪ (ℓ "亓亦") ⟫ʷ
wl1421 c4 = lw4 c4 (ℓ "亦亏亓") (ℓ "亓亦") tt tt Eq.refl

wl1422 : Base 4 → ⟪ (ℓ "丩亦") ⟫ʷ ≈ ⟪ (ℓ "亦丩") ⟫ʷ
wl1422 c4 = lw4 c4 (ℓ "丩亦") (ℓ "亦丩") tt tt Eq.refl

wl1423 : Base 4 → ⟪ (ℓ "与与") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1423 c4 = lw4 c4 (ℓ "与与") [] tt tt Eq.refl

wl1424 : Base 4 → ⟪ (ℓ "上丫") ⟫ʷ ≈ ⟪ (ℓ "丫丐") ⟫ʷ
wl1424 c4 = lw4 c4 (ℓ "上丫") (ℓ "丫丐") tt tt Eq.refl

wl1425 : Base 4 → ⟪ (ℓ "中丫") ⟫ʷ ≈ ⟪ (ℓ "丫久") ⟫ʷ
wl1425 c4 = lw4 c4 (ℓ "中丫") (ℓ "丫久") tt tt Eq.refl

wl1426 : Base 4 → ⟪ (ℓ "丐乊") ⟫ʷ ≈ ⟪ (ℓ "乊世") ⟫ʷ
wl1426 c4 = lw4 c4 (ℓ "丐乊") (ℓ "乊世") tt tt Eq.refl

wl1427 : Base 4 → ⟪ (ℓ "九丫") ⟫ʷ ≈ ⟪ (ℓ "丫习") ⟫ʷ
wl1427 c4 = lw4 c4 (ℓ "九丫") (ℓ "丫习") tt tt Eq.refl

wl1428 : Base 4 → ⟪ (ℓ "世乥") ⟫ʷ ≈ ⟪ (ℓ "乥东") ⟫ʷ
wl1428 c4 = lw4 c4 (ℓ "世乥") (ℓ "乥东") tt tt Eq.refl

wl1429 : Base 4 → ⟪ (ℓ "东乼") ⟫ʷ ≈ ⟪ (ℓ "乼丢") ⟫ʷ
wl1429 c4 = lw0 c4 (ℓ "东乼") (ℓ "乼丢") tt tt Eq.refl

wl1430 : Base 4 → ⟪ (ℓ "亦与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与亦") ⟫ʷ
wl1430 c4 = lw4 c4 (ℓ "亦与上与") (ℓ "与上与亦") tt tt Eq.refl

wl1431 : Base 4 → ⟪ (ℓ "与上与") ⟫ʷ ≈ ⟪ (ℓ "一下") ⟫ʷ
wl1431 c4 = lw4 c4 (ℓ "与上与") (ℓ "一下") tt tt Eq.refl

wl1432 : Base 4 → ⟪ (ℓ "乫亦") ⟫ʷ ≈ ⟪ (ℓ "亦乫京") ⟫ʷ
wl1432 c4 = lw0 c4 (ℓ "乫亦") (ℓ "亦乫京") tt tt Eq.refl

wl1433 : Base 4 → ⟪ (ℓ "与乫乫") ⟫ʷ ≈ ⟪ (ℓ "与") ⟫ʷ
wl1433 c4 = lw1 c4 (ℓ "与乫乫") (ℓ "与") tt tt Eq.refl

wl1434 : Base 4 → ⟪ (ℓ "乒亓与") ⟫ʷ ≈ ⟪ (ℓ "与亓") ⟫ʷ
wl1434 c4 = lw4 c4 (ℓ "乒亓与") (ℓ "与亓") tt tt Eq.refl

wl1435 : Base 4 → ⟪ (ℓ "亏亓亦") ⟫ʷ ≈ ⟪ (ℓ "亦亓") ⟫ʷ
wl1435 c4 = lw4 c4 (ℓ "亏亓亦") (ℓ "亦亓") tt tt Eq.refl

wl1436 : Base 4 → ⟪ (ℓ "亓与") ⟫ʷ ≈ ⟪ (ℓ "与乒亓") ⟫ʷ
wl1436 c4 = lw4 c4 (ℓ "亓与") (ℓ "与乒亓") tt tt Eq.refl

wl1437 : Base 4 → ⟪ (ℓ "乹与") ⟫ʷ ≈ ⟪ (ℓ "与乹") ⟫ʷ
wl1437 c4 = lw1 c4 (ℓ "乹与") (ℓ "与乹") tt tt Eq.refl

wl1438 : Base 4 → ⟪ (ℓ "乺与") ⟫ʷ ≈ ⟪ (ℓ "与乺") ⟫ʷ
wl1438 c4 = lw1 c4 (ℓ "乺与") (ℓ "与乺") tt tt Eq.refl

wl1439 : Base 4 → ⟪ (ℓ "亏与中与") ⟫ʷ ≈ ⟪ (ℓ "与中与亏") ⟫ʷ
wl1439 c4 = lw4 c4 (ℓ "亏与中与") (ℓ "与中与亏") tt tt Eq.refl

wl1440 : Base 4 → ⟪ (ℓ "中与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与中") ⟫ʷ
wl1440 c4 = lw4 c4 (ℓ "中与上与") (ℓ "与上与中") tt tt Eq.refl

wl1441 : Base 4 → ⟪ (ℓ "丒中上与") ⟫ʷ ≈ ⟪ (ℓ "与中") ⟫ʷ
wl1441 c4 = lw4 c4 (ℓ "丒中上与") (ℓ "与中") tt tt Eq.refl

wl1442 : Base 4 → ⟪ (ℓ "丒中上亏") ⟫ʷ ≈ ⟪ (ℓ "亏丒中上") ⟫ʷ
wl1442 c4 = lw4 c4 (ℓ "丒中上亏") (ℓ "亏丒中上") tt tt Eq.refl

wl1443 : Base 4 → ⟪ (ℓ "中与") ⟫ʷ ≈ ⟪ (ℓ "与丒中上") ⟫ʷ
wl1443 c4 = lw4 c4 (ℓ "中与") (ℓ "与丒中上") tt tt Eq.refl

wl1444 : Base 4 → ⟪ (ℓ "中与中与") ⟫ʷ ≈ ⟪ (ℓ "与中与中") ⟫ʷ
wl1444 c4 = lw4 c4 (ℓ "中与中与") (ℓ "与中与中") tt tt Eq.refl

wl1445 : Base 4 → ⟪ (ℓ "上与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与上") ⟫ʷ
wl1445 c4 = lw4 c4 (ℓ "上与上与") (ℓ "与上与上") tt tt Eq.refl

wl1446 : Base 4 → ⟪ (ℓ "与上") ⟫ʷ ≈ ⟪ (ℓ "一下与") ⟫ʷ
wl1446 c4 = lw4 c4 (ℓ "与上") (ℓ "一下与") tt tt Eq.refl

wl1447 : Base 4 → ⟪ (ℓ "亦一下") ⟫ʷ ≈ ⟪ (ℓ "一下亦") ⟫ʷ
wl1447 c4 = lw4 c4 (ℓ "亦一下") (ℓ "一下亦") tt tt Eq.refl

wl1448 : Base 4 → ⟪ (ℓ "上与") ⟫ʷ ≈ ⟪ (ℓ "与一下") ⟫ʷ
wl1448 c4 = lw4 c4 (ℓ "上与") (ℓ "与一下") tt tt Eq.refl

wl1449 : Base 4 → ⟪ (ℓ "上与中与") ⟫ʷ ≈ ⟪ (ℓ "与中与上") ⟫ʷ
wl1449 c4 = lw4 c4 (ℓ "上与中与") (ℓ "与中与上") tt tt Eq.refl

wl1450 : Base 4 → ⟪ (ℓ "丨与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与丨") ⟫ʷ
wl1450 c4 = lw4 c4 (ℓ "丨与上与") (ℓ "与上与丨") tt tt Eq.refl

wl1451 : Base 4 → ⟪ (ℓ "丐丩与") ⟫ʷ ≈ ⟪ (ℓ "与丨") ⟫ʷ
wl1451 c4 = lw4 c4 (ℓ "丐丩与") (ℓ "与丨") tt tt Eq.refl

wl1452 : Base 4 → ⟪ (ℓ "丐丩亦") ⟫ʷ ≈ ⟪ (ℓ "亦丐丩") ⟫ʷ
wl1452 c4 = lw4 c4 (ℓ "丐丩亦") (ℓ "亦丐丩") tt tt Eq.refl

wl1453 : Base 4 → ⟪ (ℓ "丨与") ⟫ʷ ≈ ⟪ (ℓ "与丐丩") ⟫ʷ
wl1453 c4 = lw4 c4 (ℓ "丨与") (ℓ "与丐丩") tt tt Eq.refl

wl1454 : Base 4 → ⟪ (ℓ "丨与中与") ⟫ʷ ≈ ⟪ (ℓ "与中与丨") ⟫ʷ
wl1454 c4 = lw4 c4 (ℓ "丨与中与") (ℓ "与中与丨") tt tt Eq.refl

wl1455 : Base 4 → ⟪ (ℓ "乢乥") ⟫ʷ ≈ ⟪ (ℓ "乥乢") ⟫ʷ
wl1455 c4 = lw4 c4 (ℓ "乢乥") (ℓ "乥乢") tt tt Eq.refl

wl1456 : Base 4 → ⟪ (ℓ "乼並") ⟫ʷ ≈ ⟪ (ℓ "丠乼") ⟫ʷ
wl1456 c4 = lw0 c4 (ℓ "乼並") (ℓ "丠乼") tt tt Eq.refl

wl1457 : Base 4 → ⟪ (ℓ "乥丠") ⟫ʷ ≈ ⟪ (ℓ "业乥") ⟫ʷ
wl1457 c4 = lw4 c4 (ℓ "乥丠") (ℓ "业乥") tt tt Eq.refl

wl1458 : Base 4 → ⟪ (ℓ "乊业") ⟫ʷ ≈ ⟪ (ℓ "且乊") ⟫ʷ
wl1458 c4 = lw4 c4 (ℓ "乊业") (ℓ "且乊") tt tt Eq.refl

wl1459 : Base 4 → ⟪ (ℓ "丫且") ⟫ʷ ≈ ⟪ (ℓ "与丫") ⟫ʷ
wl1459 c4 = lw4 c4 (ℓ "丫且") (ℓ "与丫") tt tt Eq.refl

wl1460 : Base 4 → ⟪ (ℓ "丒") ⟫ʷ ≈ ⟪ (ℓ "与中与中") ⟫ʷ
wl1460 c4 = lw4 c4 (ℓ "丒") (ℓ "与中与中") tt tt Eq.refl

wl1461 : Base 4 → ⟪ (ℓ "与上与上") ⟫ʷ ≈ ⟪ (ℓ "一") ⟫ʷ
wl1461 c4 = lw4 c4 (ℓ "与上与上") (ℓ "一") tt tt Eq.refl

wl1462 : Base 4 → ⟪ (ℓ "丨丫") ⟫ʷ ≈ ⟪ (ℓ "丫丨") ⟫ʷ
wl1462 c4 = lw4 c4 (ℓ "丨丫") (ℓ "丫丨") tt tt Eq.refl

wl1463 : Base 4 → ⟪ (ℓ "亄丢亄") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1463 c4 = lw0 c4 (ℓ "亄丢亄") [] tt tt Eq.refl

wl1464 : Base 4 → ⟪ (ℓ "亄亄丢") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1464 c4 = lw0 c4 (ℓ "亄亄丢") [] tt tt Eq.refl

wl1465 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "为二为") ⟫ʷ
wl1465 c4 = lw4 c4 (ℓ "二") (ℓ "为二为") tt tt Eq.refl

wl1466 : Base 4 → ⟪ (ℓ "京亳交") ⟫ʷ ≈ ⟪ (ℓ "亳京") ⟫ʷ
wl1466 c4 = lw0 c4 (ℓ "京亳交") (ℓ "亳京") tt tt Eq.refl

wl1467 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "买交买") ⟫ʷ
wl1467 c4 = lw4 c4 (ℓ "交") (ℓ "买交买") tt tt Eq.refl

wl1468 : Base 4 → ⟪ (ℓ "二买") ⟫ʷ ≈ ⟪ (ℓ "买交二") ⟫ʷ
wl1468 c4 = lw4 c4 (ℓ "二买") (ℓ "买交二") tt tt Eq.refl

wl1469 : Base 4 → ⟪ (ℓ "交为") ⟫ʷ ≈ ⟪ (ℓ "为二交") ⟫ʷ
wl1469 c4 = lw4 c4 (ℓ "交为") (ℓ "为二交") tt tt Eq.refl

wl1470 : Base 4 → ⟪ (ℓ "二交二交二") ⟫ʷ ≈ ⟪ (ℓ "二") ⟫ʷ
wl1470 c4 = lw4 c4 (ℓ "二交二交二") (ℓ "二") tt tt Eq.refl

wl1471 : Base 4 → ⟪ (ℓ "丒中上互乇互么") ⟫ʷ ≈ ⟪ (ℓ "互乇互么丒中上") ⟫ʷ
wl1471 c4 = lw4 c4 (ℓ "丒中上互乇互么") (ℓ "互乇互么丒中上") tt tt Eq.refl

wl1472 : Base 4 → ⟪ (ℓ "两京严") ⟫ʷ ≈ ⟪ (ℓ "亯") ⟫ʷ
wl1472 c4 = lw0 c4 (ℓ "两京严") (ℓ "亯") tt tt Eq.refl

wl1473 : Base 4 → ⟪ (ℓ "乏丢亯丣") ⟫ʷ ≈ ⟪ (ℓ "亯京") ⟫ʷ
wl1473 c4 = lw0 c4 (ℓ "乏丢亯丣") (ℓ "亯京") tt tt Eq.refl

wl1474 : Base 4 → ⟪ (ℓ "亯亯") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1474 c4 = lw0 c4 (ℓ "亯亯") [] tt tt Eq.refl

wl1475 : Base 4 → ⟪ (ℓ "互乇互么与临与") ⟫ʷ ≈ ⟪ (ℓ "与临与互乇互么") ⟫ʷ
wl1475 c4 = lw4 c4 (ℓ "互乇互么与临与") (ℓ "与临与互乇互么") tt tt Eq.refl

wl1476 : Base 4 → ⟪ (ℓ "中与临与") ⟫ʷ ≈ ⟪ (ℓ "与临与中") ⟫ʷ
wl1476 c4 = lw4 c4 (ℓ "中与临与") (ℓ "与临与中") tt tt Eq.refl

wl1477 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "之亐之") ⟫ʷ
wl1477 c4 = lw4 c4 (ℓ "亐") (ℓ "之亐之") tt tt Eq.refl

wl1478 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "也亘也") ⟫ʷ
wl1478 c4 = lw4 c4 (ℓ "亘") (ℓ "也亘也") tt tt Eq.refl

wl1479 : Base 4 → ⟪ (ℓ "亐也") ⟫ʷ ≈ ⟪ (ℓ "也亘亐") ⟫ʷ
wl1479 c4 = lw4 c4 (ℓ "亐也") (ℓ "也亘亐") tt tt Eq.refl

wl1480 : Base 4 → ⟪ (ℓ "亘之") ⟫ʷ ≈ ⟪ (ℓ "之亐亘") ⟫ʷ
wl1480 c4 = lw4 c4 (ℓ "亘之") (ℓ "之亐亘") tt tt Eq.refl

wl1481 : Base 4 → ⟪ (ℓ "亐亘亐亘亐") ⟫ʷ ≈ ⟪ (ℓ "亐") ⟫ʷ
wl1481 c4 = lw4 c4 (ℓ "亐亘亐亘亐") (ℓ "亐") tt tt Eq.refl

wl1482 : Base 4 → ⟪ (ℓ "京乐亯") ⟫ʷ ≈ ⟪ (ℓ "亯京") ⟫ʷ
wl1482 c4 = lw0 c4 (ℓ "京乐亯") (ℓ "亯京") tt tt Eq.refl

wl1483 : Base 4 → ⟪ (ℓ "京乐") ⟫ʷ ≈ ⟪ (ℓ "亯京亯") ⟫ʷ
wl1483 c4 = lw0 c4 (ℓ "京乐") (ℓ "亯京亯") tt tt Eq.refl

wl1484 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "乐京乐") ⟫ʷ
wl1484 c4 = lw0 c4 (ℓ "京") (ℓ "乐京乐") tt tt Eq.refl

wl1485 : Base 4 → ⟪ (ℓ "京亯") ⟫ʷ ≈ ⟪ (ℓ "亯京乐") ⟫ʷ
wl1485 c4 = lw0 c4 (ℓ "京亯") (ℓ "亯京乐") tt tt Eq.refl

wl1486 : Base 4 → ⟪ (ℓ "京乐亯京") ⟫ʷ ≈ ⟪ (ℓ "亯") ⟫ʷ
wl1486 c4 = lw0 c4 (ℓ "京乐亯京") (ℓ "亯") tt tt Eq.refl

wl1487 : Base 4 → ⟪ (ℓ "丘临上与") ⟫ʷ ≈ ⟪ (ℓ "与临") ⟫ʷ
wl1487 c4 = lw4 c4 (ℓ "丘临上与") (ℓ "与临") tt tt Eq.refl

wl1488 : Base 4 → ⟪ (ℓ "丘临上些乎些乏") ⟫ʷ ≈ ⟪ (ℓ "些乎些乏丘临上") ⟫ʷ
wl1488 c4 = lw4 c4 (ℓ "丘临上些乎些乏") (ℓ "些乎些乏丘临上") tt tt Eq.refl

wl1489 : Base 4 → ⟪ (ℓ "京丘") ⟫ʷ ≈ ⟪ (ℓ "丘京") ⟫ʷ
wl1489 c4 = lw0 c4 (ℓ "京丘") (ℓ "丘京") tt tt Eq.refl

wl1490 : Base 4 → ⟪ (ℓ "临与") ⟫ʷ ≈ ⟪ (ℓ "与丘临上") ⟫ʷ
wl1490 c4 = lw4 c4 (ℓ "临与") (ℓ "与丘临上") tt tt Eq.refl

wl1491 : Base 4 → ⟪ (ℓ "亰乤亳") ⟫ʷ ≈ ⟪ (ℓ "亳亰") ⟫ʷ
wl1491 c4 = lw0 c4 (ℓ "亰乤亳") (ℓ "亳亰") tt tt Eq.refl

wl1492 : Base 4 → ⟪ (ℓ "亰乤") ⟫ʷ ≈ ⟪ (ℓ "亳亰亳") ⟫ʷ
wl1492 c4 = lw0 c4 (ℓ "亰乤") (ℓ "亳亰亳") tt tt Eq.refl

wl1493 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "乤亰乤") ⟫ʷ
wl1493 c4 = lw0 c4 (ℓ "亰") (ℓ "乤亰乤") tt tt Eq.refl

wl1494 : Base 4 → ⟪ (ℓ "亰亳") ⟫ʷ ≈ ⟪ (ℓ "亳亰乤") ⟫ʷ
wl1494 c4 = lw0 c4 (ℓ "亰亳") (ℓ "亳亰乤") tt tt Eq.refl

wl1495 : Base 4 → ⟪ (ℓ "亰乤亳亰") ⟫ʷ ≈ ⟪ (ℓ "亳") ⟫ʷ
wl1495 c4 = lw0 c4 (ℓ "亰乤亳亰") (ℓ "亳") tt tt Eq.refl

wl1496 : Base 4 → ⟪ (ℓ "京亳") ⟫ʷ ≈ ⟪ (ℓ "亳京交") ⟫ʷ
wl1496 c4 = lw0 c4 (ℓ "京亳") (ℓ "亳京交") tt tt Eq.refl

wl1497 : Base 4 → ⟪ (ℓ "交二交二交") ⟫ʷ ≈ ⟪ (ℓ "交") ⟫ʷ
wl1497 c4 = lw4 c4 (ℓ "交二交二交") (ℓ "交") tt tt Eq.refl

wl1498 : Base 4 → ⟪ (ℓ "乫亯") ⟫ʷ ≈ ⟪ (ℓ "亯乫交") ⟫ʷ
wl1498 c4 = lw0 c4 (ℓ "乫亯") (ℓ "亯乫交") tt tt Eq.refl

wl1499 : Base 4 → ⟪ (ℓ "交亯") ⟫ʷ ≈ ⟪ (ℓ "亯交") ⟫ʷ
wl1499 c4 = lw0 c4 (ℓ "交亯") (ℓ "亯交") tt tt Eq.refl

wl1500 : Base 4 → ⟪ (ℓ "乏亯") ⟫ʷ ≈ ⟪ (ℓ "亯乏") ⟫ʷ
wl1500 c4 = lw0 c4 (ℓ "乏亯") (ℓ "亯乏") tt tt Eq.refl

wl1501 : Base 4 → ⟪ (ℓ "丞丶书丷书丯丟") ⟫ʷ ≈ ⟪ (ℓ "些") ⟫ʷ
wl1501 c4 = lw4 c4 (ℓ "丞丶书丷书丯丟") (ℓ "些") tt tt Eq.refl

wl1502 : Base 4 → ⟪ (ℓ "乎亯") ⟫ʷ ≈ ⟪ (ℓ "亯乎") ⟫ʷ
wl1502 c4 = lw0 c4 (ℓ "乎亯") (ℓ "亯乎") tt tt Eq.refl

wl1503 : Base 4 → ⟪ (ℓ "交些二乎些二乏与") ⟫ʷ ≈ ⟪ (ℓ "些二乎些二乏与交") ⟫ʷ
wl1503 c4 = lw4 c4 (ℓ "交些二乎些二乏与") (ℓ "些二乎些二乏与交") tt tt Eq.refl

wl1504 : Base 4 → ⟪ (ℓ "二乎些") ⟫ʷ ≈ ⟪ (ℓ "乎些二") ⟫ʷ
wl1504 c4 = lw4 c4 (ℓ "二乎些") (ℓ "乎些二") tt tt Eq.refl

wl1505 : Base 4 → ⟪ (ℓ "乳互与") ⟫ʷ ≈ ⟪ (ℓ "与互") ⟫ʷ
wl1505 c4 = lw4 c4 (ℓ "乳互与") (ℓ "与互") tt tt Eq.refl

wl1506 : Base 4 → ⟪ (ℓ "乳互些乎些乏") ⟫ʷ ≈ ⟪ (ℓ "些乎些乏乳互") ⟫ʷ
wl1506 c4 = lw4 c4 (ℓ "乳互些乎些乏") (ℓ "些乎些乏乳互") tt tt Eq.refl

wl1507 : Base 4 → ⟪ (ℓ "乳亳") ⟫ʷ ≈ ⟪ (ℓ "亳乳") ⟫ʷ
wl1507 c4 = lw0 c4 (ℓ "乳亳") (ℓ "亳乳") tt tt Eq.refl

wl1508 : Base 4 → ⟪ (ℓ "丒丶乄丷乄乎专") ⟫ʷ ≈ ⟪ (ℓ "互") ⟫ʷ
wl1508 c4 = lw4 c4 (ℓ "丒丶乄丷乄乎专") (ℓ "互") tt tt Eq.refl

wl1509 : Base 4 → ⟪ (ℓ "乎亳") ⟫ʷ ≈ ⟪ (ℓ "亳乎") ⟫ʷ
wl1509 c4 = lw0 c4 (ℓ "乎亳") (ℓ "亳乎") tt tt Eq.refl

wl1510 : Base 4 → ⟪ (ℓ "互与") ⟫ʷ ≈ ⟪ (ℓ "与乳互") ⟫ʷ
wl1510 c4 = lw4 c4 (ℓ "互与") (ℓ "与乳互") tt tt Eq.refl

wl1511 : Base 4 → ⟪ (ℓ "乇与") ⟫ʷ ≈ ⟪ (ℓ "与乇") ⟫ʷ
wl1511 c4 = lw4 c4 (ℓ "乇与") (ℓ "与乇") tt tt Eq.refl

wl1512 : Base 4 → ⟪ (ℓ "乇些乎些乏") ⟫ʷ ≈ ⟪ (ℓ "些乎些乏乇") ⟫ʷ
wl1512 c4 = lw4 c4 (ℓ "乇些乎些乏") (ℓ "些乎些乏乇") tt tt Eq.refl

wl1513 : Base 4 → ⟪ (ℓ "么与") ⟫ʷ ≈ ⟪ (ℓ "与么") ⟫ʷ
wl1513 c4 = lw4 c4 (ℓ "么与") (ℓ "与么") tt tt Eq.refl

wl1514 : Base 4 → ⟪ (ℓ "么些乎些乏") ⟫ʷ ≈ ⟪ (ℓ "些乎些乏么") ⟫ʷ
wl1514 c4 = lw4 c4 (ℓ "么些乎些乏") (ℓ "些乎些乏么") tt tt Eq.refl

wl1515 : Base 4 → ⟪ (ℓ "丒中上些乎些乏") ⟫ʷ ≈ ⟪ (ℓ "些乎些乏丒中上") ⟫ʷ
wl1515 c4 = lw4 c4 (ℓ "丒中上些乎些乏") (ℓ "些乎些乏丒中上") tt tt Eq.refl

wl1516 : Base 4 → ⟪ (ℓ "乗亳") ⟫ʷ ≈ ⟪ (ℓ "亳乗交") ⟫ʷ
wl1516 c4 = lw0 c4 (ℓ "乗亳") (ℓ "亳乗交") tt tt Eq.refl

wl1517 : Base 4 → ⟪ (ℓ "乏亳") ⟫ʷ ≈ ⟪ (ℓ "亳乏") ⟫ʷ
wl1517 c4 = lw0 c4 (ℓ "乏亳") (ℓ "亳乏") tt tt Eq.refl

wl1518 : Base 4 → ⟪ (ℓ "二些乎二些乏与交") ⟫ʷ ≈ ⟪ (ℓ "交二些乎二些乏与") ⟫ʷ
wl1518 c4 = lw4 c4 (ℓ "二些乎二些乏与交") (ℓ "交二些乎二些乏与") tt tt Eq.refl

wl1519 : Base 4 → ⟪ (ℓ "二些乎") ⟫ʷ ≈ ⟪ (ℓ "些乎二") ⟫ʷ
wl1519 c4 = lw4 c4 (ℓ "二些乎") (ℓ "些乎二") tt tt Eq.refl

wl1520 : Base 4 → ⟪ (ℓ "书些与") ⟫ʷ ≈ ⟪ (ℓ "与些") ⟫ʷ
wl1520 c4 = lw4 c4 (ℓ "书些与") (ℓ "与些") tt tt Eq.refl

wl1521 : Base 4 → ⟪ (ℓ "书些些乎些乏") ⟫ʷ ≈ ⟪ (ℓ "些乎些乏书些") ⟫ʷ
wl1521 c4 = lw4 c4 (ℓ "书些些乎些乏") (ℓ "些乎些乏书些") tt tt Eq.refl

wl1522 : Base 4 → ⟪ (ℓ "乭书亳") ⟫ʷ ≈ ⟪ (ℓ "亳书") ⟫ʷ
wl1522 c4 = lw0 c4 (ℓ "乭书亳") (ℓ "亳书") tt tt Eq.refl

wl1523 : Base 4 → ⟪ (ℓ "乭亳") ⟫ʷ ≈ ⟪ (ℓ "亳乭") ⟫ʷ
wl1523 c4 = lw0 c4 (ℓ "乭亳") (ℓ "亳乭") tt tt Eq.refl

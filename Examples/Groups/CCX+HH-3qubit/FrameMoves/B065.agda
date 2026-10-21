{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B065 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0347 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1247 ; K1256 ; K1257 ; K1267 ; K1345 ; K1347 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2347 ; K2367 ; K2567 ; M1 ; M3 ; M5 ; M6 ; M7 ; X01 ; X13 ; X15 ; X16 ; X17 ; _•_ ; _≈_ ; by-assoc-and ; m0 ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00000)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00255 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00293 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383 ; module MV00420 ; module MV00438)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00010 ; module MV00011 ; module MV00012 ; module MV00013 ; module MV00024 ; module MV00032 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00048 ; module MV00057 ; module MV00058 ; module MV00059 ; module MV00060 ; module MV00061 ; module MV00113)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00129 ; module MV00137)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00259 ; module MV00260 ; module MV00261 ; module MV00265 ; module MV00266 ; module MV00267 ; module MV00271 ; module MV00278 ; module MV00282 ; module MV00283 ; module MV00285 ; module MV00289 ; module MV00290 ; module MV00295)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00298 ; module MV00300 ; module MV00302 ; module MV00304 ; module MV00307 ; module MV00310 ; module MV00311 ; module MV00314 ; module MV00315 ; module MV00316 ; module MV00321 ; module MV00322 ; module MV00323 ; module MV00327)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00334 ; module MV00338 ; module MV00339 ; module MV00341 ; module MV00344 ; module MV00345 ; module MV00346 ; module MV00352 ; module MV00358 ; module MV00360 ; module MV00365 ; module MV00366)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00370 ; module MV00371 ; module MV00376 ; module MV00377 ; module MV00379 ; module MV00384 ; module MV00385 ; module MV00390 ; module MV00397)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00401 ; module MV00402 ; module MV00407 ; module MV00413 ; module MV00415 ; module MV00421 ; module MV00425)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00429 ; module MV00430 ; module MV00435 ; module MV00436 ; module MV00441 ; module MV00442 ; module MV00443 ; module MV00446 ; module MV00452 ; module MV00455)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B010 using (module MV00456 ; module MV00458 ; module MV00460 ; module MV00461 ; module MV00462 ; module MV00467 ; module MV00472 ; module MV00474 ; module MV00478 ; module MV00479 ; module MV00482 ; module MV00483)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00487 ; module MV00488 ; module MV00490 ; module MV00493 ; module MV00494 ; module MV00495 ; module MV00500 ; module MV00507 ; module MV00511 ; module MV00512)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00517 ; module MV00523 ; module MV00525 ; module MV00530 ; module MV00531 ; module MV00535)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00540 ; module MV00546 ; module MV00548 ; module MV00552 ; module MV00553 ; module MV00557 ; module MV00563)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00566 ; module MV00567 ; module MV00578 ; module MV00582 ; module MV00583)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00600 ; module MV00605)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00000 ; module PE00956)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B018 using (module PE01371)

module MV02499 where

  proved : p (s1 • s2 • s3 • s2 • s1) • K0157 ≈ K0457 • p (s1 • s2 • s3 • s2 • s1)
  proved = by-assoc-and (move-compose MV00429.proved (move-compose MV00430.proved (move-compose MV00413.proved (move-compose MV00376.proved (MV00314.proved))))) Eq.refl Eq.refl

module MV02500 where

  proved : p (s1 • s2 • s3 • s2 • s1) • K0167 ≈ K0467 • p (s1 • s2 • s3 • s2 • s1)
  proved = by-assoc-and (move-compose MV00435.proved (move-compose MV00436.proved (move-compose MV00420.proved (move-compose MV00383.proved (MV00320.proved))))) Eq.refl Eq.refl

module MV02501 where

  proved : p (s1 • s2 • s3 • s4 • s3 • s2 • s1) • K0167 ≈ K0567 • p (s1 • s2 • s3 • s4 • s3 • s2 • s1)
  proved = by-assoc-and (move-compose MV00441.proved (move-compose MV00442.proved (move-compose MV00443.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (MV00320.proved))))))) Eq.refl Eq.refl

module MV02502 where

  proved : p (s2 • s3 • s2) • K0256 ≈ K0456 • p (s2 • s3 • s2)
  proved = by-assoc-and (move-compose MV00425.proved (move-compose MV00407.proved (MV00370.proved))) Eq.refl Eq.refl

module MV02503 where

  proved : p (s2 • s3 • s2) • K0257 ≈ K0457 • p (s2 • s3 • s2)
  proved = by-assoc-and (move-compose MV00430.proved (move-compose MV00413.proved (MV00376.proved))) Eq.refl Eq.refl

module MV02504 where

  proved : p (s2 • s3 • s2) • K0267 ≈ K0467 • p (s2 • s3 • s2)
  proved = by-assoc-and (move-compose MV00436.proved (move-compose MV00420.proved (MV00383.proved))) Eq.refl Eq.refl

module MV02505 where

  proved : p (s2 • s3 • s4 • s3 • s2) • K0267 ≈ K0567 • p (s2 • s3 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00442.proved (move-compose MV00443.proved (move-compose MV00438.proved (move-compose MV00420.proved (MV00383.proved))))) Eq.refl Eq.refl

module MV02506 where

  proved : p (s3 • s4 • s3) • K0367 ≈ K0567 • p (s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00443.proved (move-compose MV00438.proved (MV00420.proved))) Eq.refl Eq.refl

module MV02507 where

  proved : p (s2 • s3 • s2) • K1256 ≈ K1456 • p (s2 • s3 • s2)
  proved = by-assoc-and (move-compose MV00535.proved (move-compose MV00517.proved (MV00482.proved))) Eq.refl Eq.refl

module MV02508 where

  proved : p (s2 • s3 • s2) • K1257 ≈ K1457 • p (s2 • s3 • s2)
  proved = by-assoc-and (move-compose MV00540.proved (move-compose MV00523.proved (MV00487.proved))) Eq.refl Eq.refl

module MV02509 where

  proved : p (s2 • s3 • s2) • K1267 ≈ K1467 • p (s2 • s3 • s2)
  proved = by-assoc-and (move-compose MV00546.proved (move-compose MV00530.proved (MV00493.proved))) Eq.refl Eq.refl

module MV02510 where

  proved : p (s2 • s3 • s4 • s3 • s2) • K1267 ≈ K1567 • p (s2 • s3 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00552.proved (move-compose MV00553.proved (move-compose MV00548.proved (move-compose MV00530.proved (MV00493.proved))))) Eq.refl Eq.refl

module MV02511 where

  proved : p (s3 • s4 • s3) • K1367 ≈ K1567 • p (s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00553.proved (move-compose MV00548.proved (MV00530.proved))) Eq.refl Eq.refl

module MV02512 where

  proved : p (s3 • s4 • s3) • K2367 ≈ K2567 • p (s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00605.proved (move-compose MV00600.proved (MV00582.proved))) Eq.refl Eq.refl

module MV02513 where

  proved : p (s2 • s3 • s2) • K0125 ≈ K0145 • p (s2 • s3 • s2)
  proved = by-assoc-and (move-compose MV00293.proved (move-compose MV00276.proved (MV00254.proved))) Eq.refl Eq.refl

module MV02514 where

  proved : p (s2 • s3 • s2) • K0126 ≈ K0146 • p (s2 • s3 • s2)
  proved = by-assoc-and (move-compose MV00298.proved (move-compose MV00282.proved (MV00259.proved))) Eq.refl Eq.refl

module MV02515 where

  proved : p (s2 • s3 • s2) • K0127 ≈ K0147 • p (s2 • s3 • s2)
  proved = by-assoc-and (move-compose MV00304.proved (move-compose MV00288.proved (MV00264.proved))) Eq.refl Eq.refl

module MV02516 where

  proved : p (s2 • s3 • s4 • s3 • s2) • K0126 ≈ K0156 • p (s2 • s3 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00310.proved (move-compose MV00311.proved (move-compose MV00300.proved (move-compose MV00282.proved (MV00259.proved))))) Eq.refl Eq.refl

module MV02517 where

  proved : p (s2 • s3 • s4 • s3 • s2) • K0127 ≈ K0157 • p (s2 • s3 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00315.proved (move-compose MV00316.proved (move-compose MV00306.proved (move-compose MV00288.proved (MV00264.proved))))) Eq.refl Eq.refl

module MV02518 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2) • K0127 ≈ K0167 • p (s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00321.proved (move-compose MV00322.proved (move-compose MV00323.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (MV00264.proved))))))) Eq.refl Eq.refl

module MV02519 where

  proved : p (s3 • s4 • s3) • K0136 ≈ K0156 • p (s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00311.proved (move-compose MV00300.proved (MV00282.proved))) Eq.refl Eq.refl

module MV02520 where

  proved : p (s3 • s4 • s3) • K0137 ≈ K0157 • p (s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00316.proved (move-compose MV00306.proved (MV00288.proved))) Eq.refl Eq.refl

module MV02521 where

  proved : p (s3 • s4 • s5 • s4 • s3) • K0137 ≈ K0167 • p (s3 • s4 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00322.proved (move-compose MV00323.proved (move-compose MV00318.proved (move-compose MV00306.proved (MV00288.proved))))) Eq.refl Eq.refl

module MV02522 where

  proved : p (s4 • s5 • s4) • K0147 ≈ K0167 • p (s4 • s5 • s4)
  proved = by-assoc-and (move-compose MV00323.proved (move-compose MV00318.proved (MV00306.proved))) Eq.refl Eq.refl

module MV02523 where

  proved : p (s3 • s4 • s3) • K0236 ≈ K0256 • p (s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00371.proved (move-compose MV00358.proved (MV00338.proved))) Eq.refl Eq.refl

module MV02524 where

  proved : p (s3 • s4 • s3) • K0237 ≈ K0257 • p (s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00377.proved (move-compose MV00365.proved (MV00344.proved))) Eq.refl Eq.refl

module MV02525 where

  proved : p (s3 • s4 • s5 • s4 • s3) • K0237 ≈ K0267 • p (s3 • s4 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00384.proved (move-compose MV00385.proved (move-compose MV00379.proved (move-compose MV00365.proved (MV00344.proved))))) Eq.refl Eq.refl

module MV02526 where

  proved : p (s4 • s5 • s4) • K0247 ≈ K0267 • p (s4 • s5 • s4)
  proved = by-assoc-and (move-compose MV00385.proved (move-compose MV00379.proved (MV00365.proved))) Eq.refl Eq.refl

module MV02527 where

  proved : p (s4 • s5 • s4) • K0347 ≈ K0367 • p (s4 • s5 • s4)
  proved = by-assoc-and (move-compose MV00421.proved (move-compose MV00415.proved (MV00401.proved))) Eq.refl Eq.refl

module MV02528 where

  proved : p (s3 • s4 • s3) • K1236 ≈ K1256 • p (s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00483.proved (move-compose MV00472.proved (MV00455.proved))) Eq.refl Eq.refl

module MV02529 where

  proved : p (s3 • s4 • s3) • K1237 ≈ K1257 • p (s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00488.proved (move-compose MV00478.proved (MV00460.proved))) Eq.refl Eq.refl

module MV02530 where

  proved : p (s3 • s4 • s5 • s4 • s3) • K1237 ≈ K1267 • p (s3 • s4 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00494.proved (move-compose MV00495.proved (move-compose MV00490.proved (move-compose MV00478.proved (MV00460.proved))))) Eq.refl Eq.refl

module MV02531 where

  proved : p (s4 • s5 • s4) • K1247 ≈ K1267 • p (s4 • s5 • s4)
  proved = by-assoc-and (move-compose MV00495.proved (move-compose MV00490.proved (MV00478.proved))) Eq.refl Eq.refl

module MV02532 where

  proved : p (s4 • s5 • s4) • K1347 ≈ K1367 • p (s4 • s5 • s4)
  proved = by-assoc-and (move-compose MV00531.proved (move-compose MV00525.proved (MV00511.proved))) Eq.refl Eq.refl

module MV02533 where

  proved : p (s4 • s5 • s4) • K2347 ≈ K2367 • p (s4 • s5 • s4)
  proved = by-assoc-and (move-compose MV00583.proved (move-compose MV00578.proved (MV00566.proved))) Eq.refl Eq.refl

module MV02534 where

  proved : p (s3 • s4 • s3) • K0123 ≈ K0125 • p (s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00255.proved (move-compose MV00251.proved (MV00245.proved))) Eq.refl Eq.refl

module MV02535 where

  proved : p (s3 • s4 • s5 • s4 • s3) • K0123 ≈ K0126 • p (s3 • s4 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00260.proved (move-compose MV00261.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))) Eq.refl Eq.refl

module MV02536 where

  proved : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • K0123 ≈ K0127 • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00265.proved (move-compose MV00266.proved (move-compose MV00267.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))) Eq.refl Eq.refl

module MV02537 where

  proved : p (s4 • s5 • s4) • K0124 ≈ K0126 • p (s4 • s5 • s4)
  proved = by-assoc-and (move-compose MV00261.proved (move-compose MV00257.proved (MV00251.proved))) Eq.refl Eq.refl

module MV02538 where

  proved : p (s4 • s5 • s6 • s5 • s4) • K0124 ≈ K0127 • p (s4 • s5 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00266.proved (move-compose MV00267.proved (move-compose MV00263.proved (move-compose MV00257.proved (MV00251.proved))))) Eq.refl Eq.refl

module MV02539 where

  proved : p (s5 • s6 • s5) • K0125 ≈ K0127 • p (s5 • s6 • s5)
  proved = by-assoc-and (move-compose MV00267.proved (move-compose MV00263.proved (MV00257.proved))) Eq.refl Eq.refl

module MV02540 where

  proved : p (s4 • s5 • s4) • K0134 ≈ K0136 • p (s4 • s5 • s4)
  proved = by-assoc-and (move-compose MV00283.proved (move-compose MV00278.proved (MV00271.proved))) Eq.refl Eq.refl

module MV02541 where

  proved : p (s4 • s5 • s6 • s5 • s4) • K0134 ≈ K0137 • p (s4 • s5 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00289.proved (move-compose MV00290.proved (move-compose MV00285.proved (move-compose MV00278.proved (MV00271.proved))))) Eq.refl Eq.refl

module MV02542 where

  proved : p (s5 • s6 • s5) • K0135 ≈ K0137 • p (s5 • s6 • s5)
  proved = by-assoc-and (move-compose MV00290.proved (move-compose MV00285.proved (MV00278.proved))) Eq.refl Eq.refl

module MV02543 where

  proved : p (s5 • s6 • s5) • K0145 ≈ K0147 • p (s5 • s6 • s5)
  proved = by-assoc-and (move-compose MV00307.proved (move-compose MV00302.proved (MV00295.proved))) Eq.refl Eq.refl

module MV02544 where

  proved : p (s4 • s5 • s4) • K0234 ≈ K0236 • p (s4 • s5 • s4)
  proved = by-assoc-and (move-compose MV00339.proved (move-compose MV00334.proved (MV00327.proved))) Eq.refl Eq.refl

module MV02545 where

  proved : p (s4 • s5 • s6 • s5 • s4) • K0234 ≈ K0237 • p (s4 • s5 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00345.proved (move-compose MV00346.proved (move-compose MV00341.proved (move-compose MV00334.proved (MV00327.proved))))) Eq.refl Eq.refl

module MV02546 where

  proved : p (s5 • s6 • s5) • K0235 ≈ K0237 • p (s5 • s6 • s5)
  proved = by-assoc-and (move-compose MV00346.proved (move-compose MV00341.proved (MV00334.proved))) Eq.refl Eq.refl

module MV02547 where

  proved : p (s5 • s6 • s5) • K0245 ≈ K0247 • p (s5 • s6 • s5)
  proved = by-assoc-and (move-compose MV00366.proved (move-compose MV00360.proved (MV00352.proved))) Eq.refl Eq.refl

module MV02548 where

  proved : p (s5 • s6 • s5) • K0345 ≈ K0347 • p (s5 • s6 • s5)
  proved = by-assoc-and (move-compose MV00402.proved (move-compose MV00397.proved (MV00390.proved))) Eq.refl Eq.refl

module MV02549 where

  proved : p (s4 • s5 • s4) • K1234 ≈ K1236 • p (s4 • s5 • s4)
  proved = by-assoc-and (move-compose MV00456.proved (move-compose MV00452.proved (MV00446.proved))) Eq.refl Eq.refl

module MV02550 where

  proved : p (s4 • s5 • s6 • s5 • s4) • K1234 ≈ K1237 • p (s4 • s5 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00461.proved (move-compose MV00462.proved (move-compose MV00458.proved (move-compose MV00452.proved (MV00446.proved))))) Eq.refl Eq.refl

module MV02551 where

  proved : p (s5 • s6 • s5) • K1235 ≈ K1237 • p (s5 • s6 • s5)
  proved = by-assoc-and (move-compose MV00462.proved (move-compose MV00458.proved (MV00452.proved))) Eq.refl Eq.refl

module MV02552 where

  proved : p (s5 • s6 • s5) • K1245 ≈ K1247 • p (s5 • s6 • s5)
  proved = by-assoc-and (move-compose MV00479.proved (move-compose MV00474.proved (MV00467.proved))) Eq.refl Eq.refl

module MV02553 where

  proved : p (s5 • s6 • s5) • K1345 ≈ K1347 • p (s5 • s6 • s5)
  proved = by-assoc-and (move-compose MV00512.proved (move-compose MV00507.proved (MV00500.proved))) Eq.refl Eq.refl

module MV02554 where

  proved : p (s5 • s6 • s5) • K2345 ≈ K2347 • p (s5 • s6 • s5)
  proved = by-assoc-and (move-compose MV00567.proved (move-compose MV00563.proved (MV00557.proved))) Eq.refl Eq.refl

module MV02555 where

  proved : p (ε) • X01 ≈ X01 • p (ε)
  proved = by-assoc-and PE00000.proved Eq.refl Eq.refl

module MV02556 where

  proved : p (ε) • X13 ≈ X13 • p (ε)
  proved = by-assoc-and PE00956.proved Eq.refl Eq.refl

module MV02557 where

  step0 : p (ε) • M1 ≈ p (s0) • p (ε) • m0 • p (s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0)) PE00000.proved) Eq.refl Eq.refl

  step1 : p (s0) • p (ε) • m0 • p (s0) ≈ p (s0) • m0 • p (ε) • p (s0)
  step1 = by-assoc-and (under (p (s0)) (p (s0)) CM00000.proved) Eq.refl Eq.refl

  step2 : p (s0) • m0 • p (ε) • p (s0) ≈ M1 • p (ε)
  step2 = by-assoc-and (under (p (s0) • m0) (ε) PE00000.proved) Eq.refl Eq.refl

  proved : p (ε) • M1 ≈ M1 • p (ε)
  proved = trans step0 (trans step1 step2)

module MV02558 where

  step0 : p (ε) • M3 ≈ p (s0 • s1 • s2 • s1 • s0) • p (ε) • m0 • p (s0 • s1 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s1 • s0)) PE01371.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s0) • p (ε) • m0 • p (s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0) • m0 • p (ε) • p (s0 • s1 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s1 • s0)) CM00000.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s0) • m0 • p (ε) • p (s0 • s1 • s2 • s1 • s0) ≈ M3 • p (ε)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0) • m0) (ε) PE01371.proved) Eq.refl Eq.refl

  proved : p (ε) • M3 ≈ M3 • p (ε)
  proved = trans step0 (trans step1 step2)

module MV02559 where

  proved : p (s4 • s3) • X01 ≈ X01 • p (s4 • s3)
  proved = by-assoc-and (move-compose MV00059.proved (MV00058.proved)) Eq.refl Eq.refl

module MV02560 where

  proved : p (s4 • s3) • X13 ≈ X15 • p (s4 • s3)
  proved = by-assoc-and (move-compose MV00121.proved (MV00113.proved)) Eq.refl Eq.refl

module MV02561 where

  proved : p (s4 • s3) • M1 ≈ M1 • p (s4 • s3)
  proved = by-assoc-and (move-compose MV00011.proved (MV00010.proved)) Eq.refl Eq.refl

module MV02562 where

  proved : p (s4 • s3) • M3 ≈ M5 • p (s4 • s3)
  proved = by-assoc-and (move-compose MV00032.proved (MV00024.proved)) Eq.refl Eq.refl

module MV02563 where

  proved : p (s5 • s4 • s3) • X01 ≈ X01 • p (s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))) Eq.refl Eq.refl

module MV02564 where

  proved : p (s5 • s4 • s3) • X13 ≈ X16 • p (s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))) Eq.refl Eq.refl

module MV02565 where

  proved : p (s5 • s4 • s3) • M1 ≈ M1 • p (s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))) Eq.refl Eq.refl

module MV02566 where

  proved : p (s5 • s4 • s3) • M3 ≈ M6 • p (s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))) Eq.refl Eq.refl

module MV02567 where

  proved : p (s6 • s5 • s4 • s3) • X01 ≈ X01 • p (s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))) Eq.refl Eq.refl

module MV02568 where

  proved : p (s6 • s5 • s4 • s3) • X13 ≈ X17 • p (s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))) Eq.refl Eq.refl

module MV02569 where

  proved : p (s6 • s5 • s4 • s3) • M1 ≈ M1 • p (s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))) Eq.refl Eq.refl

module MV02570 where

  proved : p (s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))) Eq.refl Eq.refl

module MV02571 where

  proved : p (s2 • s3) • X01 ≈ X01 • p (s2 • s3)
  proved = by-assoc-and (move-compose MV00057.proved (MV00058.proved)) Eq.refl Eq.refl

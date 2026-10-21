{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0456 ; K0457 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1456 ; K1457 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2456 ; K2457 ; K3456 ; K3457 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00257 ; module MV00263)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00271 ; module MV00278 ; module MV00285 ; module MV00295)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00302 ; module MV00313 ; module MV00327)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00334 ; module MV00341 ; module MV00352 ; module MV00360)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00373 ; module MV00390 ; module MV00397)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00409)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00427 ; module MV00446 ; module MV00452)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B010 using (module MV00458 ; module MV00467 ; module MV00474 ; module MV00485)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00500 ; module MV00507)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00519 ; module MV00537)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00557 ; module MV00563)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00573 ; module MV00589)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00610)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B065 using (module MV02534 ; module MV02535 ; module MV02536 ; module MV02537 ; module MV02538 ; module MV02539 ; module MV02540 ; module MV02541 ; module MV02542 ; module MV02543 ; module MV02544 ; module MV02545 ; module MV02546 ; module MV02547 ; module MV02548 ; module MV02549 ; module MV02550 ; module MV02551 ; module MV02552 ; module MV02553 ; module MV02554)

module r3g_ij01234 where

  proved : X34 • K0123 ≈ K0124 • X34
  proved = by-assoc-and MV00245.proved Eq.refl Eq.refl

module r3g_ij01235 where

  proved : X35 • K0123 ≈ K0125 • X35
  proved = by-assoc-and MV02534.proved Eq.refl Eq.refl

module r3g_ij01236 where

  proved : X36 • K0123 ≈ K0126 • X36
  proved = by-assoc-and MV02535.proved Eq.refl Eq.refl

module r3g_ij01237 where

  proved : X37 • K0123 ≈ K0127 • X37
  proved = by-assoc-and MV02536.proved Eq.refl Eq.refl

module r3g_ij01245 where

  proved : X45 • K0124 ≈ K0125 • X45
  proved = by-assoc-and MV00251.proved Eq.refl Eq.refl

module r3g_ij01246 where

  proved : X46 • K0124 ≈ K0126 • X46
  proved = by-assoc-and MV02537.proved Eq.refl Eq.refl

module r3g_ij01247 where

  proved : X47 • K0124 ≈ K0127 • X47
  proved = by-assoc-and MV02538.proved Eq.refl Eq.refl

module r3g_ij01256 where

  proved : X56 • K0125 ≈ K0126 • X56
  proved = by-assoc-and MV00257.proved Eq.refl Eq.refl

module r3g_ij01257 where

  proved : X57 • K0125 ≈ K0127 • X57
  proved = by-assoc-and MV02539.proved Eq.refl Eq.refl

module r3g_ij01267 where

  proved : X67 • K0126 ≈ K0127 • X67
  proved = by-assoc-and MV00263.proved Eq.refl Eq.refl

module r3g_ij01345 where

  proved : X45 • K0134 ≈ K0135 • X45
  proved = by-assoc-and MV00271.proved Eq.refl Eq.refl

module r3g_ij01346 where

  proved : X46 • K0134 ≈ K0136 • X46
  proved = by-assoc-and MV02540.proved Eq.refl Eq.refl

module r3g_ij01347 where

  proved : X47 • K0134 ≈ K0137 • X47
  proved = by-assoc-and MV02541.proved Eq.refl Eq.refl

module r3g_ij01356 where

  proved : X56 • K0135 ≈ K0136 • X56
  proved = by-assoc-and MV00278.proved Eq.refl Eq.refl

module r3g_ij01357 where

  proved : X57 • K0135 ≈ K0137 • X57
  proved = by-assoc-and MV02542.proved Eq.refl Eq.refl

module r3g_ij01367 where

  proved : X67 • K0136 ≈ K0137 • X67
  proved = by-assoc-and MV00285.proved Eq.refl Eq.refl

module r3g_ij01456 where

  proved : X56 • K0145 ≈ K0146 • X56
  proved = by-assoc-and MV00295.proved Eq.refl Eq.refl

module r3g_ij01457 where

  proved : X57 • K0145 ≈ K0147 • X57
  proved = by-assoc-and MV02543.proved Eq.refl Eq.refl

module r3g_ij01467 where

  proved : X67 • K0146 ≈ K0147 • X67
  proved = by-assoc-and MV00302.proved Eq.refl Eq.refl

module r3g_ij01567 where

  proved : X67 • K0156 ≈ K0157 • X67
  proved = by-assoc-and MV00313.proved Eq.refl Eq.refl

module r3g_ij02345 where

  proved : X45 • K0234 ≈ K0235 • X45
  proved = by-assoc-and MV00327.proved Eq.refl Eq.refl

module r3g_ij02346 where

  proved : X46 • K0234 ≈ K0236 • X46
  proved = by-assoc-and MV02544.proved Eq.refl Eq.refl

module r3g_ij02347 where

  proved : X47 • K0234 ≈ K0237 • X47
  proved = by-assoc-and MV02545.proved Eq.refl Eq.refl

module r3g_ij02356 where

  proved : X56 • K0235 ≈ K0236 • X56
  proved = by-assoc-and MV00334.proved Eq.refl Eq.refl

module r3g_ij02357 where

  proved : X57 • K0235 ≈ K0237 • X57
  proved = by-assoc-and MV02546.proved Eq.refl Eq.refl

module r3g_ij02367 where

  proved : X67 • K0236 ≈ K0237 • X67
  proved = by-assoc-and MV00341.proved Eq.refl Eq.refl

module r3g_ij02456 where

  proved : X56 • K0245 ≈ K0246 • X56
  proved = by-assoc-and MV00352.proved Eq.refl Eq.refl

module r3g_ij02457 where

  proved : X57 • K0245 ≈ K0247 • X57
  proved = by-assoc-and MV02547.proved Eq.refl Eq.refl

module r3g_ij02467 where

  proved : X67 • K0246 ≈ K0247 • X67
  proved = by-assoc-and MV00360.proved Eq.refl Eq.refl

module r3g_ij02567 where

  proved : X67 • K0256 ≈ K0257 • X67
  proved = by-assoc-and MV00373.proved Eq.refl Eq.refl

module r3g_ij03456 where

  proved : X56 • K0345 ≈ K0346 • X56
  proved = by-assoc-and MV00390.proved Eq.refl Eq.refl

module r3g_ij03457 where

  proved : X57 • K0345 ≈ K0347 • X57
  proved = by-assoc-and MV02548.proved Eq.refl Eq.refl

module r3g_ij03467 where

  proved : X67 • K0346 ≈ K0347 • X67
  proved = by-assoc-and MV00397.proved Eq.refl Eq.refl

module r3g_ij03567 where

  proved : X67 • K0356 ≈ K0357 • X67
  proved = by-assoc-and MV00409.proved Eq.refl Eq.refl

module r3g_ij04567 where

  proved : X67 • K0456 ≈ K0457 • X67
  proved = by-assoc-and MV00427.proved Eq.refl Eq.refl

module r3g_ij12345 where

  proved : X45 • K1234 ≈ K1235 • X45
  proved = by-assoc-and MV00446.proved Eq.refl Eq.refl

module r3g_ij12346 where

  proved : X46 • K1234 ≈ K1236 • X46
  proved = by-assoc-and MV02549.proved Eq.refl Eq.refl

module r3g_ij12347 where

  proved : X47 • K1234 ≈ K1237 • X47
  proved = by-assoc-and MV02550.proved Eq.refl Eq.refl

module r3g_ij12356 where

  proved : X56 • K1235 ≈ K1236 • X56
  proved = by-assoc-and MV00452.proved Eq.refl Eq.refl

module r3g_ij12357 where

  proved : X57 • K1235 ≈ K1237 • X57
  proved = by-assoc-and MV02551.proved Eq.refl Eq.refl

module r3g_ij12367 where

  proved : X67 • K1236 ≈ K1237 • X67
  proved = by-assoc-and MV00458.proved Eq.refl Eq.refl

module r3g_ij12456 where

  proved : X56 • K1245 ≈ K1246 • X56
  proved = by-assoc-and MV00467.proved Eq.refl Eq.refl

module r3g_ij12457 where

  proved : X57 • K1245 ≈ K1247 • X57
  proved = by-assoc-and MV02552.proved Eq.refl Eq.refl

module r3g_ij12467 where

  proved : X67 • K1246 ≈ K1247 • X67
  proved = by-assoc-and MV00474.proved Eq.refl Eq.refl

module r3g_ij12567 where

  proved : X67 • K1256 ≈ K1257 • X67
  proved = by-assoc-and MV00485.proved Eq.refl Eq.refl

module r3g_ij13456 where

  proved : X56 • K1345 ≈ K1346 • X56
  proved = by-assoc-and MV00500.proved Eq.refl Eq.refl

module r3g_ij13457 where

  proved : X57 • K1345 ≈ K1347 • X57
  proved = by-assoc-and MV02553.proved Eq.refl Eq.refl

module r3g_ij13467 where

  proved : X67 • K1346 ≈ K1347 • X67
  proved = by-assoc-and MV00507.proved Eq.refl Eq.refl

module r3g_ij13567 where

  proved : X67 • K1356 ≈ K1357 • X67
  proved = by-assoc-and MV00519.proved Eq.refl Eq.refl

module r3g_ij14567 where

  proved : X67 • K1456 ≈ K1457 • X67
  proved = by-assoc-and MV00537.proved Eq.refl Eq.refl

module r3g_ij23456 where

  proved : X56 • K2345 ≈ K2346 • X56
  proved = by-assoc-and MV00557.proved Eq.refl Eq.refl

module r3g_ij23457 where

  proved : X57 • K2345 ≈ K2347 • X57
  proved = by-assoc-and MV02554.proved Eq.refl Eq.refl

module r3g_ij23467 where

  proved : X67 • K2346 ≈ K2347 • X67
  proved = by-assoc-and MV00563.proved Eq.refl Eq.refl

module r3g_ij23567 where

  proved : X67 • K2356 ≈ K2357 • X67
  proved = by-assoc-and MV00573.proved Eq.refl Eq.refl

module r3g_ij24567 where

  proved : X67 • K2456 ≈ K2457 • X67
  proved = by-assoc-and MV00589.proved Eq.refl Eq.refl

module r3g_ij34567 where

  proved : X67 • K3456 ≈ K3457 • X67
  proved = by-assoc-and MV00610.proved Eq.refl Eq.refl

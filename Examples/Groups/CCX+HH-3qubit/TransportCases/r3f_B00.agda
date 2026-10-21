{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0457 ; K0467 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1457 ; K1467 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2457 ; K2467 ; K3457 ; K3467 ; X23 ; X24 ; X25 ; X26 ; X34 ; X35 ; X36 ; X45 ; X46 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00254 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00306 ; module MV00318)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00249 ; module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00300 ; module MV00332)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00338 ; module MV00344 ; module MV00358 ; module MV00365)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00379 ; module MV00395)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00401 ; module MV00415)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00432 ; module MV00450 ; module MV00455)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B010 using (module MV00460 ; module MV00472 ; module MV00478)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00490 ; module MV00505 ; module MV00511)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00525)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00542 ; module MV00561)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00566 ; module MV00578)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00594)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00614)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B065 using (module MV02513 ; module MV02514 ; module MV02515 ; module MV02516 ; module MV02517 ; module MV02518 ; module MV02519 ; module MV02520 ; module MV02521 ; module MV02522 ; module MV02523 ; module MV02524 ; module MV02525 ; module MV02526 ; module MV02527 ; module MV02528 ; module MV02529 ; module MV02530 ; module MV02531 ; module MV02532 ; module MV02533)

module r3f_ij01234 where

  proved : X23 • K0124 ≈ K0134 • X23
  proved = by-assoc-and MV00249.proved Eq.refl Eq.refl

module r3f_ij01235 where

  proved : X23 • K0125 ≈ K0135 • X23
  proved = by-assoc-and MV00254.proved Eq.refl Eq.refl

module r3f_ij01236 where

  proved : X23 • K0126 ≈ K0136 • X23
  proved = by-assoc-and MV00259.proved Eq.refl Eq.refl

module r3f_ij01237 where

  proved : X23 • K0127 ≈ K0137 • X23
  proved = by-assoc-and MV00264.proved Eq.refl Eq.refl

module r3f_ij01245 where

  proved : X24 • K0125 ≈ K0145 • X24
  proved = by-assoc-and MV02513.proved Eq.refl Eq.refl

module r3f_ij01246 where

  proved : X24 • K0126 ≈ K0146 • X24
  proved = by-assoc-and MV02514.proved Eq.refl Eq.refl

module r3f_ij01247 where

  proved : X24 • K0127 ≈ K0147 • X24
  proved = by-assoc-and MV02515.proved Eq.refl Eq.refl

module r3f_ij01256 where

  proved : X25 • K0126 ≈ K0156 • X25
  proved = by-assoc-and MV02516.proved Eq.refl Eq.refl

module r3f_ij01257 where

  proved : X25 • K0127 ≈ K0157 • X25
  proved = by-assoc-and MV02517.proved Eq.refl Eq.refl

module r3f_ij01267 where

  proved : X26 • K0127 ≈ K0167 • X26
  proved = by-assoc-and MV02518.proved Eq.refl Eq.refl

module r3f_ij01345 where

  proved : X34 • K0135 ≈ K0145 • X34
  proved = by-assoc-and MV00276.proved Eq.refl Eq.refl

module r3f_ij01346 where

  proved : X34 • K0136 ≈ K0146 • X34
  proved = by-assoc-and MV00282.proved Eq.refl Eq.refl

module r3f_ij01347 where

  proved : X34 • K0137 ≈ K0147 • X34
  proved = by-assoc-and MV00288.proved Eq.refl Eq.refl

module r3f_ij01356 where

  proved : X35 • K0136 ≈ K0156 • X35
  proved = by-assoc-and MV02519.proved Eq.refl Eq.refl

module r3f_ij01357 where

  proved : X35 • K0137 ≈ K0157 • X35
  proved = by-assoc-and MV02520.proved Eq.refl Eq.refl

module r3f_ij01367 where

  proved : X36 • K0137 ≈ K0167 • X36
  proved = by-assoc-and MV02521.proved Eq.refl Eq.refl

module r3f_ij01456 where

  proved : X45 • K0146 ≈ K0156 • X45
  proved = by-assoc-and MV00300.proved Eq.refl Eq.refl

module r3f_ij01457 where

  proved : X45 • K0147 ≈ K0157 • X45
  proved = by-assoc-and MV00306.proved Eq.refl Eq.refl

module r3f_ij01467 where

  proved : X46 • K0147 ≈ K0167 • X46
  proved = by-assoc-and MV02522.proved Eq.refl Eq.refl

module r3f_ij01567 where

  proved : X56 • K0157 ≈ K0167 • X56
  proved = by-assoc-and MV00318.proved Eq.refl Eq.refl

module r3f_ij02345 where

  proved : X34 • K0235 ≈ K0245 • X34
  proved = by-assoc-and MV00332.proved Eq.refl Eq.refl

module r3f_ij02346 where

  proved : X34 • K0236 ≈ K0246 • X34
  proved = by-assoc-and MV00338.proved Eq.refl Eq.refl

module r3f_ij02347 where

  proved : X34 • K0237 ≈ K0247 • X34
  proved = by-assoc-and MV00344.proved Eq.refl Eq.refl

module r3f_ij02356 where

  proved : X35 • K0236 ≈ K0256 • X35
  proved = by-assoc-and MV02523.proved Eq.refl Eq.refl

module r3f_ij02357 where

  proved : X35 • K0237 ≈ K0257 • X35
  proved = by-assoc-and MV02524.proved Eq.refl Eq.refl

module r3f_ij02367 where

  proved : X36 • K0237 ≈ K0267 • X36
  proved = by-assoc-and MV02525.proved Eq.refl Eq.refl

module r3f_ij02456 where

  proved : X45 • K0246 ≈ K0256 • X45
  proved = by-assoc-and MV00358.proved Eq.refl Eq.refl

module r3f_ij02457 where

  proved : X45 • K0247 ≈ K0257 • X45
  proved = by-assoc-and MV00365.proved Eq.refl Eq.refl

module r3f_ij02467 where

  proved : X46 • K0247 ≈ K0267 • X46
  proved = by-assoc-and MV02526.proved Eq.refl Eq.refl

module r3f_ij02567 where

  proved : X56 • K0257 ≈ K0267 • X56
  proved = by-assoc-and MV00379.proved Eq.refl Eq.refl

module r3f_ij03456 where

  proved : X45 • K0346 ≈ K0356 • X45
  proved = by-assoc-and MV00395.proved Eq.refl Eq.refl

module r3f_ij03457 where

  proved : X45 • K0347 ≈ K0357 • X45
  proved = by-assoc-and MV00401.proved Eq.refl Eq.refl

module r3f_ij03467 where

  proved : X46 • K0347 ≈ K0367 • X46
  proved = by-assoc-and MV02527.proved Eq.refl Eq.refl

module r3f_ij03567 where

  proved : X56 • K0357 ≈ K0367 • X56
  proved = by-assoc-and MV00415.proved Eq.refl Eq.refl

module r3f_ij04567 where

  proved : X56 • K0457 ≈ K0467 • X56
  proved = by-assoc-and MV00432.proved Eq.refl Eq.refl

module r3f_ij12345 where

  proved : X34 • K1235 ≈ K1245 • X34
  proved = by-assoc-and MV00450.proved Eq.refl Eq.refl

module r3f_ij12346 where

  proved : X34 • K1236 ≈ K1246 • X34
  proved = by-assoc-and MV00455.proved Eq.refl Eq.refl

module r3f_ij12347 where

  proved : X34 • K1237 ≈ K1247 • X34
  proved = by-assoc-and MV00460.proved Eq.refl Eq.refl

module r3f_ij12356 where

  proved : X35 • K1236 ≈ K1256 • X35
  proved = by-assoc-and MV02528.proved Eq.refl Eq.refl

module r3f_ij12357 where

  proved : X35 • K1237 ≈ K1257 • X35
  proved = by-assoc-and MV02529.proved Eq.refl Eq.refl

module r3f_ij12367 where

  proved : X36 • K1237 ≈ K1267 • X36
  proved = by-assoc-and MV02530.proved Eq.refl Eq.refl

module r3f_ij12456 where

  proved : X45 • K1246 ≈ K1256 • X45
  proved = by-assoc-and MV00472.proved Eq.refl Eq.refl

module r3f_ij12457 where

  proved : X45 • K1247 ≈ K1257 • X45
  proved = by-assoc-and MV00478.proved Eq.refl Eq.refl

module r3f_ij12467 where

  proved : X46 • K1247 ≈ K1267 • X46
  proved = by-assoc-and MV02531.proved Eq.refl Eq.refl

module r3f_ij12567 where

  proved : X56 • K1257 ≈ K1267 • X56
  proved = by-assoc-and MV00490.proved Eq.refl Eq.refl

module r3f_ij13456 where

  proved : X45 • K1346 ≈ K1356 • X45
  proved = by-assoc-and MV00505.proved Eq.refl Eq.refl

module r3f_ij13457 where

  proved : X45 • K1347 ≈ K1357 • X45
  proved = by-assoc-and MV00511.proved Eq.refl Eq.refl

module r3f_ij13467 where

  proved : X46 • K1347 ≈ K1367 • X46
  proved = by-assoc-and MV02532.proved Eq.refl Eq.refl

module r3f_ij13567 where

  proved : X56 • K1357 ≈ K1367 • X56
  proved = by-assoc-and MV00525.proved Eq.refl Eq.refl

module r3f_ij14567 where

  proved : X56 • K1457 ≈ K1467 • X56
  proved = by-assoc-and MV00542.proved Eq.refl Eq.refl

module r3f_ij23456 where

  proved : X45 • K2346 ≈ K2356 • X45
  proved = by-assoc-and MV00561.proved Eq.refl Eq.refl

module r3f_ij23457 where

  proved : X45 • K2347 ≈ K2357 • X45
  proved = by-assoc-and MV00566.proved Eq.refl Eq.refl

module r3f_ij23467 where

  proved : X46 • K2347 ≈ K2367 • X46
  proved = by-assoc-and MV02533.proved Eq.refl Eq.refl

module r3f_ij23567 where

  proved : X56 • K2357 ≈ K2367 • X56
  proved = by-assoc-and MV00578.proved Eq.refl Eq.refl

module r3f_ij24567 where

  proved : X56 • K2457 ≈ K2467 • X56
  proved = by-assoc-and MV00594.proved Eq.refl Eq.refl

module r3f_ij34567 where

  proved : X56 • K3457 ≈ K3467 • X56
  proved = by-assoc-and MV00614.proved Eq.refl Eq.refl

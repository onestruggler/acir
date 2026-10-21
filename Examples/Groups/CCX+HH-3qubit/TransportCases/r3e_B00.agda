{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3467 ; K3567 ; X12 ; X13 ; X14 ; X15 ; X23 ; X24 ; X25 ; X34 ; X35 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00292 ; module MV00320 ; module MV00350 ; module MV00383 ; module MV00420 ; module MV00438)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00269 ; module MV00274 ; module MV00280 ; module MV00286)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00303 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00356 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00370 ; module MV00376)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00407 ; module MV00413)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B010 using (module MV00465 ; module MV00470 ; module MV00476 ; module MV00482)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00487 ; module MV00493)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00517 ; module MV00523 ; module MV00530)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00548)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00571 ; module MV00576 ; module MV00582)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00600)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00619)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B064 using (module MV02492 ; module MV02493 ; module MV02494 ; module MV02495 ; module MV02496 ; module MV02497 ; module MV02498)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B065 using (module MV02499 ; module MV02500 ; module MV02501 ; module MV02502 ; module MV02503 ; module MV02504 ; module MV02505 ; module MV02506 ; module MV02507 ; module MV02508 ; module MV02509 ; module MV02510 ; module MV02511 ; module MV02512)

module r3e_ij01234 where

  proved : X12 • K0134 ≈ K0234 • X12
  proved = by-assoc-and MV00269.proved Eq.refl Eq.refl

module r3e_ij01235 where

  proved : X12 • K0135 ≈ K0235 • X12
  proved = by-assoc-and MV00274.proved Eq.refl Eq.refl

module r3e_ij01236 where

  proved : X12 • K0136 ≈ K0236 • X12
  proved = by-assoc-and MV00280.proved Eq.refl Eq.refl

module r3e_ij01237 where

  proved : X12 • K0137 ≈ K0237 • X12
  proved = by-assoc-and MV00286.proved Eq.refl Eq.refl

module r3e_ij01245 where

  proved : X12 • K0145 ≈ K0245 • X12
  proved = by-assoc-and MV00292.proved Eq.refl Eq.refl

module r3e_ij01246 where

  proved : X12 • K0146 ≈ K0246 • X12
  proved = by-assoc-and MV00297.proved Eq.refl Eq.refl

module r3e_ij01247 where

  proved : X12 • K0147 ≈ K0247 • X12
  proved = by-assoc-and MV00303.proved Eq.refl Eq.refl

module r3e_ij01256 where

  proved : X12 • K0156 ≈ K0256 • X12
  proved = by-assoc-and MV00309.proved Eq.refl Eq.refl

module r3e_ij01257 where

  proved : X12 • K0157 ≈ K0257 • X12
  proved = by-assoc-and MV00314.proved Eq.refl Eq.refl

module r3e_ij01267 where

  proved : X12 • K0167 ≈ K0267 • X12
  proved = by-assoc-and MV00320.proved Eq.refl Eq.refl

module r3e_ij01345 where

  proved : X13 • K0145 ≈ K0345 • X13
  proved = by-assoc-and MV02492.proved Eq.refl Eq.refl

module r3e_ij01346 where

  proved : X13 • K0146 ≈ K0346 • X13
  proved = by-assoc-and MV02493.proved Eq.refl Eq.refl

module r3e_ij01347 where

  proved : X13 • K0147 ≈ K0347 • X13
  proved = by-assoc-and MV02494.proved Eq.refl Eq.refl

module r3e_ij01356 where

  proved : X13 • K0156 ≈ K0356 • X13
  proved = by-assoc-and MV02495.proved Eq.refl Eq.refl

module r3e_ij01357 where

  proved : X13 • K0157 ≈ K0357 • X13
  proved = by-assoc-and MV02496.proved Eq.refl Eq.refl

module r3e_ij01367 where

  proved : X13 • K0167 ≈ K0367 • X13
  proved = by-assoc-and MV02497.proved Eq.refl Eq.refl

module r3e_ij01456 where

  proved : X14 • K0156 ≈ K0456 • X14
  proved = by-assoc-and MV02498.proved Eq.refl Eq.refl

module r3e_ij01457 where

  proved : X14 • K0157 ≈ K0457 • X14
  proved = by-assoc-and MV02499.proved Eq.refl Eq.refl

module r3e_ij01467 where

  proved : X14 • K0167 ≈ K0467 • X14
  proved = by-assoc-and MV02500.proved Eq.refl Eq.refl

module r3e_ij01567 where

  proved : X15 • K0167 ≈ K0567 • X15
  proved = by-assoc-and MV02501.proved Eq.refl Eq.refl

module r3e_ij02345 where

  proved : X23 • K0245 ≈ K0345 • X23
  proved = by-assoc-and MV00350.proved Eq.refl Eq.refl

module r3e_ij02346 where

  proved : X23 • K0246 ≈ K0346 • X23
  proved = by-assoc-and MV00356.proved Eq.refl Eq.refl

module r3e_ij02347 where

  proved : X23 • K0247 ≈ K0347 • X23
  proved = by-assoc-and MV00363.proved Eq.refl Eq.refl

module r3e_ij02356 where

  proved : X23 • K0256 ≈ K0356 • X23
  proved = by-assoc-and MV00370.proved Eq.refl Eq.refl

module r3e_ij02357 where

  proved : X23 • K0257 ≈ K0357 • X23
  proved = by-assoc-and MV00376.proved Eq.refl Eq.refl

module r3e_ij02367 where

  proved : X23 • K0267 ≈ K0367 • X23
  proved = by-assoc-and MV00383.proved Eq.refl Eq.refl

module r3e_ij02456 where

  proved : X24 • K0256 ≈ K0456 • X24
  proved = by-assoc-and MV02502.proved Eq.refl Eq.refl

module r3e_ij02457 where

  proved : X24 • K0257 ≈ K0457 • X24
  proved = by-assoc-and MV02503.proved Eq.refl Eq.refl

module r3e_ij02467 where

  proved : X24 • K0267 ≈ K0467 • X24
  proved = by-assoc-and MV02504.proved Eq.refl Eq.refl

module r3e_ij02567 where

  proved : X25 • K0267 ≈ K0567 • X25
  proved = by-assoc-and MV02505.proved Eq.refl Eq.refl

module r3e_ij03456 where

  proved : X34 • K0356 ≈ K0456 • X34
  proved = by-assoc-and MV00407.proved Eq.refl Eq.refl

module r3e_ij03457 where

  proved : X34 • K0357 ≈ K0457 • X34
  proved = by-assoc-and MV00413.proved Eq.refl Eq.refl

module r3e_ij03467 where

  proved : X34 • K0367 ≈ K0467 • X34
  proved = by-assoc-and MV00420.proved Eq.refl Eq.refl

module r3e_ij03567 where

  proved : X35 • K0367 ≈ K0567 • X35
  proved = by-assoc-and MV02506.proved Eq.refl Eq.refl

module r3e_ij04567 where

  proved : X45 • K0467 ≈ K0567 • X45
  proved = by-assoc-and MV00438.proved Eq.refl Eq.refl

module r3e_ij12345 where

  proved : X23 • K1245 ≈ K1345 • X23
  proved = by-assoc-and MV00465.proved Eq.refl Eq.refl

module r3e_ij12346 where

  proved : X23 • K1246 ≈ K1346 • X23
  proved = by-assoc-and MV00470.proved Eq.refl Eq.refl

module r3e_ij12347 where

  proved : X23 • K1247 ≈ K1347 • X23
  proved = by-assoc-and MV00476.proved Eq.refl Eq.refl

module r3e_ij12356 where

  proved : X23 • K1256 ≈ K1356 • X23
  proved = by-assoc-and MV00482.proved Eq.refl Eq.refl

module r3e_ij12357 where

  proved : X23 • K1257 ≈ K1357 • X23
  proved = by-assoc-and MV00487.proved Eq.refl Eq.refl

module r3e_ij12367 where

  proved : X23 • K1267 ≈ K1367 • X23
  proved = by-assoc-and MV00493.proved Eq.refl Eq.refl

module r3e_ij12456 where

  proved : X24 • K1256 ≈ K1456 • X24
  proved = by-assoc-and MV02507.proved Eq.refl Eq.refl

module r3e_ij12457 where

  proved : X24 • K1257 ≈ K1457 • X24
  proved = by-assoc-and MV02508.proved Eq.refl Eq.refl

module r3e_ij12467 where

  proved : X24 • K1267 ≈ K1467 • X24
  proved = by-assoc-and MV02509.proved Eq.refl Eq.refl

module r3e_ij12567 where

  proved : X25 • K1267 ≈ K1567 • X25
  proved = by-assoc-and MV02510.proved Eq.refl Eq.refl

module r3e_ij13456 where

  proved : X34 • K1356 ≈ K1456 • X34
  proved = by-assoc-and MV00517.proved Eq.refl Eq.refl

module r3e_ij13457 where

  proved : X34 • K1357 ≈ K1457 • X34
  proved = by-assoc-and MV00523.proved Eq.refl Eq.refl

module r3e_ij13467 where

  proved : X34 • K1367 ≈ K1467 • X34
  proved = by-assoc-and MV00530.proved Eq.refl Eq.refl

module r3e_ij13567 where

  proved : X35 • K1367 ≈ K1567 • X35
  proved = by-assoc-and MV02511.proved Eq.refl Eq.refl

module r3e_ij14567 where

  proved : X45 • K1467 ≈ K1567 • X45
  proved = by-assoc-and MV00548.proved Eq.refl Eq.refl

module r3e_ij23456 where

  proved : X34 • K2356 ≈ K2456 • X34
  proved = by-assoc-and MV00571.proved Eq.refl Eq.refl

module r3e_ij23457 where

  proved : X34 • K2357 ≈ K2457 • X34
  proved = by-assoc-and MV00576.proved Eq.refl Eq.refl

module r3e_ij23467 where

  proved : X34 • K2367 ≈ K2467 • X34
  proved = by-assoc-and MV00582.proved Eq.refl Eq.refl

module r3e_ij23567 where

  proved : X35 • K2367 ≈ K2567 • X35
  proved = by-assoc-and MV02512.proved Eq.refl Eq.refl

module r3e_ij24567 where

  proved : X45 • K2467 ≈ K2567 • X45
  proved = by-assoc-and MV00600.proved Eq.refl Eq.refl

module r3e_ij34567 where

  proved : X45 • K3467 ≈ K3567 • X45
  proved = by-assoc-and MV00619.proved Eq.refl Eq.refl

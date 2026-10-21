{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; X01 ; X02 ; X03 ; X04 ; X12 ; X13 ; X14 ; X23 ; X24 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00387 ; module MV00440 ; module MV00498 ; module MV00551 ; module MV00604 ; module MV00624)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00325 ; module MV00330)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00336 ; module MV00342 ; module MV00348 ; module MV00354 ; module MV00361)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00368 ; module MV00374 ; module MV00381 ; module MV00392 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00404 ; module MV00410 ; module MV00417 ; module MV00423)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428 ; module MV00434)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00503 ; module MV00509)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00515 ; module MV00521 ; module MV00528 ; module MV00534 ; module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00545)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00587)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00592 ; module MV00598)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B064 using (module MV02471 ; module MV02472 ; module MV02473 ; module MV02474 ; module MV02475 ; module MV02476 ; module MV02477 ; module MV02478 ; module MV02479 ; module MV02480 ; module MV02481 ; module MV02482 ; module MV02483 ; module MV02484 ; module MV02485 ; module MV02486 ; module MV02487 ; module MV02488 ; module MV02489 ; module MV02490 ; module MV02491)

module r3d_ij01234 where

  proved : X01 • K0234 ≈ K1234 • X01
  proved = by-assoc-and MV00325.proved Eq.refl Eq.refl

module r3d_ij01235 where

  proved : X01 • K0235 ≈ K1235 • X01
  proved = by-assoc-and MV00330.proved Eq.refl Eq.refl

module r3d_ij01236 where

  proved : X01 • K0236 ≈ K1236 • X01
  proved = by-assoc-and MV00336.proved Eq.refl Eq.refl

module r3d_ij01237 where

  proved : X01 • K0237 ≈ K1237 • X01
  proved = by-assoc-and MV00342.proved Eq.refl Eq.refl

module r3d_ij01245 where

  proved : X01 • K0245 ≈ K1245 • X01
  proved = by-assoc-and MV00348.proved Eq.refl Eq.refl

module r3d_ij01246 where

  proved : X01 • K0246 ≈ K1246 • X01
  proved = by-assoc-and MV00354.proved Eq.refl Eq.refl

module r3d_ij01247 where

  proved : X01 • K0247 ≈ K1247 • X01
  proved = by-assoc-and MV00361.proved Eq.refl Eq.refl

module r3d_ij01256 where

  proved : X01 • K0256 ≈ K1256 • X01
  proved = by-assoc-and MV00368.proved Eq.refl Eq.refl

module r3d_ij01257 where

  proved : X01 • K0257 ≈ K1257 • X01
  proved = by-assoc-and MV00374.proved Eq.refl Eq.refl

module r3d_ij01267 where

  proved : X01 • K0267 ≈ K1267 • X01
  proved = by-assoc-and MV00381.proved Eq.refl Eq.refl

module r3d_ij01345 where

  proved : X01 • K0345 ≈ K1345 • X01
  proved = by-assoc-and MV00387.proved Eq.refl Eq.refl

module r3d_ij01346 where

  proved : X01 • K0346 ≈ K1346 • X01
  proved = by-assoc-and MV00392.proved Eq.refl Eq.refl

module r3d_ij01347 where

  proved : X01 • K0347 ≈ K1347 • X01
  proved = by-assoc-and MV00398.proved Eq.refl Eq.refl

module r3d_ij01356 where

  proved : X01 • K0356 ≈ K1356 • X01
  proved = by-assoc-and MV00404.proved Eq.refl Eq.refl

module r3d_ij01357 where

  proved : X01 • K0357 ≈ K1357 • X01
  proved = by-assoc-and MV00410.proved Eq.refl Eq.refl

module r3d_ij01367 where

  proved : X01 • K0367 ≈ K1367 • X01
  proved = by-assoc-and MV00417.proved Eq.refl Eq.refl

module r3d_ij01456 where

  proved : X01 • K0456 ≈ K1456 • X01
  proved = by-assoc-and MV00423.proved Eq.refl Eq.refl

module r3d_ij01457 where

  proved : X01 • K0457 ≈ K1457 • X01
  proved = by-assoc-and MV00428.proved Eq.refl Eq.refl

module r3d_ij01467 where

  proved : X01 • K0467 ≈ K1467 • X01
  proved = by-assoc-and MV00434.proved Eq.refl Eq.refl

module r3d_ij01567 where

  proved : X01 • K0567 ≈ K1567 • X01
  proved = by-assoc-and MV00440.proved Eq.refl Eq.refl

module r3d_ij02345 where

  proved : X02 • K0345 ≈ K2345 • X02
  proved = by-assoc-and MV02471.proved Eq.refl Eq.refl

module r3d_ij02346 where

  proved : X02 • K0346 ≈ K2346 • X02
  proved = by-assoc-and MV02472.proved Eq.refl Eq.refl

module r3d_ij02347 where

  proved : X02 • K0347 ≈ K2347 • X02
  proved = by-assoc-and MV02473.proved Eq.refl Eq.refl

module r3d_ij02356 where

  proved : X02 • K0356 ≈ K2356 • X02
  proved = by-assoc-and MV02474.proved Eq.refl Eq.refl

module r3d_ij02357 where

  proved : X02 • K0357 ≈ K2357 • X02
  proved = by-assoc-and MV02475.proved Eq.refl Eq.refl

module r3d_ij02367 where

  proved : X02 • K0367 ≈ K2367 • X02
  proved = by-assoc-and MV02476.proved Eq.refl Eq.refl

module r3d_ij02456 where

  proved : X02 • K0456 ≈ K2456 • X02
  proved = by-assoc-and MV02477.proved Eq.refl Eq.refl

module r3d_ij02457 where

  proved : X02 • K0457 ≈ K2457 • X02
  proved = by-assoc-and MV02478.proved Eq.refl Eq.refl

module r3d_ij02467 where

  proved : X02 • K0467 ≈ K2467 • X02
  proved = by-assoc-and MV02479.proved Eq.refl Eq.refl

module r3d_ij02567 where

  proved : X02 • K0567 ≈ K2567 • X02
  proved = by-assoc-and MV02480.proved Eq.refl Eq.refl

module r3d_ij03456 where

  proved : X03 • K0456 ≈ K3456 • X03
  proved = by-assoc-and MV02481.proved Eq.refl Eq.refl

module r3d_ij03457 where

  proved : X03 • K0457 ≈ K3457 • X03
  proved = by-assoc-and MV02482.proved Eq.refl Eq.refl

module r3d_ij03467 where

  proved : X03 • K0467 ≈ K3467 • X03
  proved = by-assoc-and MV02483.proved Eq.refl Eq.refl

module r3d_ij03567 where

  proved : X03 • K0567 ≈ K3567 • X03
  proved = by-assoc-and MV02484.proved Eq.refl Eq.refl

module r3d_ij04567 where

  proved : X04 • K0567 ≈ K4567 • X04
  proved = by-assoc-and MV02485.proved Eq.refl Eq.refl

module r3d_ij12345 where

  proved : X12 • K1345 ≈ K2345 • X12
  proved = by-assoc-and MV00498.proved Eq.refl Eq.refl

module r3d_ij12346 where

  proved : X12 • K1346 ≈ K2346 • X12
  proved = by-assoc-and MV00503.proved Eq.refl Eq.refl

module r3d_ij12347 where

  proved : X12 • K1347 ≈ K2347 • X12
  proved = by-assoc-and MV00509.proved Eq.refl Eq.refl

module r3d_ij12356 where

  proved : X12 • K1356 ≈ K2356 • X12
  proved = by-assoc-and MV00515.proved Eq.refl Eq.refl

module r3d_ij12357 where

  proved : X12 • K1357 ≈ K2357 • X12
  proved = by-assoc-and MV00521.proved Eq.refl Eq.refl

module r3d_ij12367 where

  proved : X12 • K1367 ≈ K2367 • X12
  proved = by-assoc-and MV00528.proved Eq.refl Eq.refl

module r3d_ij12456 where

  proved : X12 • K1456 ≈ K2456 • X12
  proved = by-assoc-and MV00534.proved Eq.refl Eq.refl

module r3d_ij12457 where

  proved : X12 • K1457 ≈ K2457 • X12
  proved = by-assoc-and MV00539.proved Eq.refl Eq.refl

module r3d_ij12467 where

  proved : X12 • K1467 ≈ K2467 • X12
  proved = by-assoc-and MV00545.proved Eq.refl Eq.refl

module r3d_ij12567 where

  proved : X12 • K1567 ≈ K2567 • X12
  proved = by-assoc-and MV00551.proved Eq.refl Eq.refl

module r3d_ij13456 where

  proved : X13 • K1456 ≈ K3456 • X13
  proved = by-assoc-and MV02486.proved Eq.refl Eq.refl

module r3d_ij13457 where

  proved : X13 • K1457 ≈ K3457 • X13
  proved = by-assoc-and MV02487.proved Eq.refl Eq.refl

module r3d_ij13467 where

  proved : X13 • K1467 ≈ K3467 • X13
  proved = by-assoc-and MV02488.proved Eq.refl Eq.refl

module r3d_ij13567 where

  proved : X13 • K1567 ≈ K3567 • X13
  proved = by-assoc-and MV02489.proved Eq.refl Eq.refl

module r3d_ij14567 where

  proved : X14 • K1567 ≈ K4567 • X14
  proved = by-assoc-and MV02490.proved Eq.refl Eq.refl

module r3d_ij23456 where

  proved : X23 • K2456 ≈ K3456 • X23
  proved = by-assoc-and MV00587.proved Eq.refl Eq.refl

module r3d_ij23457 where

  proved : X23 • K2457 ≈ K3457 • X23
  proved = by-assoc-and MV00592.proved Eq.refl Eq.refl

module r3d_ij23467 where

  proved : X23 • K2467 ≈ K3467 • X23
  proved = by-assoc-and MV00598.proved Eq.refl Eq.refl

module r3d_ij23567 where

  proved : X23 • K2567 ≈ K3567 • X23
  proved = by-assoc-and MV00604.proved Eq.refl Eq.refl

module r3d_ij24567 where

  proved : X24 • K2567 ≈ K4567 • X24
  proved = by-assoc-and MV02491.proved Eq.refl Eq.refl

module r3d_ij34567 where

  proved : X34 • K3567 ≈ K4567 • X34
  proved = by-assoc-and MV00624.proved Eq.refl Eq.refl

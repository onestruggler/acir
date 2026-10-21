{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X01 ; X02 ; X03 ; X04 ; X05 ; X06 ; X07 ; X12 ; X13 ; X14 ; X15 ; X16 ; X17 ; X23 ; X24 ; X25 ; X26 ; X27 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00007 ; module MV00015 ; module MV00023 ; module MV00031 ; module MV00039)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00047 ; module MV00055)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B064 using (module MV02450 ; module MV02451 ; module MV02452 ; module MV02453 ; module MV02454 ; module MV02455 ; module MV02456 ; module MV02457 ; module MV02458 ; module MV02459 ; module MV02460 ; module MV02461 ; module MV02462 ; module MV02463 ; module MV02464 ; module MV02465 ; module MV02466 ; module MV02467 ; module MV02468 ; module MV02469 ; module MV02470)

module r3c_ij01 where

  proved : X01 • M1 ≈ M0 • X01
  proved = by-assoc-and MV00007.proved Eq.refl Eq.refl

module r3c_ij02 where

  proved : X02 • M2 ≈ M0 • X02
  proved = by-assoc-and MV02450.proved Eq.refl Eq.refl

module r3c_ij03 where

  proved : X03 • M3 ≈ M0 • X03
  proved = by-assoc-and MV02451.proved Eq.refl Eq.refl

module r3c_ij04 where

  proved : X04 • M4 ≈ M0 • X04
  proved = by-assoc-and MV02452.proved Eq.refl Eq.refl

module r3c_ij05 where

  proved : X05 • M5 ≈ M0 • X05
  proved = by-assoc-and MV02453.proved Eq.refl Eq.refl

module r3c_ij06 where

  proved : X06 • M6 ≈ M0 • X06
  proved = by-assoc-and MV02454.proved Eq.refl Eq.refl

module r3c_ij07 where

  proved : X07 • M7 ≈ M0 • X07
  proved = by-assoc-and MV02455.proved Eq.refl Eq.refl

module r3c_ij12 where

  proved : X12 • M2 ≈ M1 • X12
  proved = by-assoc-and MV00015.proved Eq.refl Eq.refl

module r3c_ij13 where

  proved : X13 • M3 ≈ M1 • X13
  proved = by-assoc-and MV02456.proved Eq.refl Eq.refl

module r3c_ij14 where

  proved : X14 • M4 ≈ M1 • X14
  proved = by-assoc-and MV02457.proved Eq.refl Eq.refl

module r3c_ij15 where

  proved : X15 • M5 ≈ M1 • X15
  proved = by-assoc-and MV02458.proved Eq.refl Eq.refl

module r3c_ij16 where

  proved : X16 • M6 ≈ M1 • X16
  proved = by-assoc-and MV02459.proved Eq.refl Eq.refl

module r3c_ij17 where

  proved : X17 • M7 ≈ M1 • X17
  proved = by-assoc-and MV02460.proved Eq.refl Eq.refl

module r3c_ij23 where

  proved : X23 • M3 ≈ M2 • X23
  proved = by-assoc-and MV00023.proved Eq.refl Eq.refl

module r3c_ij24 where

  proved : X24 • M4 ≈ M2 • X24
  proved = by-assoc-and MV02461.proved Eq.refl Eq.refl

module r3c_ij25 where

  proved : X25 • M5 ≈ M2 • X25
  proved = by-assoc-and MV02462.proved Eq.refl Eq.refl

module r3c_ij26 where

  proved : X26 • M6 ≈ M2 • X26
  proved = by-assoc-and MV02463.proved Eq.refl Eq.refl

module r3c_ij27 where

  proved : X27 • M7 ≈ M2 • X27
  proved = by-assoc-and MV02464.proved Eq.refl Eq.refl

module r3c_ij34 where

  proved : X34 • M4 ≈ M3 • X34
  proved = by-assoc-and MV00031.proved Eq.refl Eq.refl

module r3c_ij35 where

  proved : X35 • M5 ≈ M3 • X35
  proved = by-assoc-and MV02465.proved Eq.refl Eq.refl

module r3c_ij36 where

  proved : X36 • M6 ≈ M3 • X36
  proved = by-assoc-and MV02466.proved Eq.refl Eq.refl

module r3c_ij37 where

  proved : X37 • M7 ≈ M3 • X37
  proved = by-assoc-and MV02467.proved Eq.refl Eq.refl

module r3c_ij45 where

  proved : X45 • M5 ≈ M4 • X45
  proved = by-assoc-and MV00039.proved Eq.refl Eq.refl

module r3c_ij46 where

  proved : X46 • M6 ≈ M4 • X46
  proved = by-assoc-and MV02468.proved Eq.refl Eq.refl

module r3c_ij47 where

  proved : X47 • M7 ≈ M4 • X47
  proved = by-assoc-and MV02469.proved Eq.refl Eq.refl

module r3c_ij56 where

  proved : X56 • M6 ≈ M5 • X56
  proved = by-assoc-and MV00047.proved Eq.refl Eq.refl

module r3c_ij57 where

  proved : X57 • M7 ≈ M5 • X57
  proved = by-assoc-and MV02470.proved Eq.refl Eq.refl

module r3c_ij67 where

  proved : X67 • M7 ≈ M6 • X67
  proved = by-assoc-and MV00055.proved Eq.refl Eq.refl

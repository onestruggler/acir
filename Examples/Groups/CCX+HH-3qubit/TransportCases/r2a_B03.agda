{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_B03 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X02 ; X03 ; X04 ; X05 ; X06 ; X12 ; X13 ; X14 ; X15 ; X16 ; X23 ; X24 ; X25 ; X26 ; X34 ; X35 ; X36 ; X45 ; X46 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00014 ; module PE00022 ; module PE00030 ; module PE00038 ; module PE00046)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B002 using (module PE00074 ; module PE00081 ; module PE00088 ; module PE00095)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B003 using (module PE00115 ; module PE00122 ; module PE00129 ; module PE00149 ; module PE00156 ; module PE00176)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B024 using (module PE01284 ; module PE01285 ; module PE01286 ; module PE01287 ; module PE01288 ; module PE01289 ; module PE01290 ; module PE01291 ; module PE01292 ; module PE01293 ; module PE01294 ; module PE01295 ; module PE01296 ; module PE01297 ; module PE01298)

module r2a_ij5701 where

  proved : X57 • X01 ≈ X01 • X57
  proved = by-assoc-and PE01284.proved Eq.refl Eq.refl

module r2a_ij5702 where

  proved : X57 • X02 ≈ X02 • X57
  proved = by-assoc-and PE01285.proved Eq.refl Eq.refl

module r2a_ij5703 where

  proved : X57 • X03 ≈ X03 • X57
  proved = by-assoc-and PE01286.proved Eq.refl Eq.refl

module r2a_ij5704 where

  proved : X57 • X04 ≈ X04 • X57
  proved = by-assoc-and PE01287.proved Eq.refl Eq.refl

module r2a_ij5706 where

  proved : X57 • X06 ≈ X06 • X57
  proved = by-assoc-and PE01288.proved Eq.refl Eq.refl

module r2a_ij5712 where

  proved : X57 • X12 ≈ X12 • X57
  proved = by-assoc-and PE01289.proved Eq.refl Eq.refl

module r2a_ij5713 where

  proved : X57 • X13 ≈ X13 • X57
  proved = by-assoc-and PE01290.proved Eq.refl Eq.refl

module r2a_ij5714 where

  proved : X57 • X14 ≈ X14 • X57
  proved = by-assoc-and PE01291.proved Eq.refl Eq.refl

module r2a_ij5716 where

  proved : X57 • X16 ≈ X16 • X57
  proved = by-assoc-and PE01292.proved Eq.refl Eq.refl

module r2a_ij5723 where

  proved : X57 • X23 ≈ X23 • X57
  proved = by-assoc-and PE01293.proved Eq.refl Eq.refl

module r2a_ij5724 where

  proved : X57 • X24 ≈ X24 • X57
  proved = by-assoc-and PE01294.proved Eq.refl Eq.refl

module r2a_ij5726 where

  proved : X57 • X26 ≈ X26 • X57
  proved = by-assoc-and PE01295.proved Eq.refl Eq.refl

module r2a_ij5734 where

  proved : X57 • X34 ≈ X34 • X57
  proved = by-assoc-and PE01296.proved Eq.refl Eq.refl

module r2a_ij5736 where

  proved : X57 • X36 ≈ X36 • X57
  proved = by-assoc-and PE01297.proved Eq.refl Eq.refl

module r2a_ij5746 where

  proved : X57 • X46 ≈ X46 • X57
  proved = by-assoc-and PE01298.proved Eq.refl Eq.refl

module r2a_ij6701 where

  proved : X67 • X01 ≈ X01 • X67
  proved = by-assoc-and PE00014.proved Eq.refl Eq.refl

module r2a_ij6702 where

  proved : X67 • X02 ≈ X02 • X67
  proved = by-assoc-and PE00022.proved Eq.refl Eq.refl

module r2a_ij6703 where

  proved : X67 • X03 ≈ X03 • X67
  proved = by-assoc-and PE00030.proved Eq.refl Eq.refl

module r2a_ij6704 where

  proved : X67 • X04 ≈ X04 • X67
  proved = by-assoc-and PE00038.proved Eq.refl Eq.refl

module r2a_ij6705 where

  proved : X67 • X05 ≈ X05 • X67
  proved = by-assoc-and PE00046.proved Eq.refl Eq.refl

module r2a_ij6712 where

  proved : X67 • X12 ≈ X12 • X67
  proved = by-assoc-and PE00074.proved Eq.refl Eq.refl

module r2a_ij6713 where

  proved : X67 • X13 ≈ X13 • X67
  proved = by-assoc-and PE00081.proved Eq.refl Eq.refl

module r2a_ij6714 where

  proved : X67 • X14 ≈ X14 • X67
  proved = by-assoc-and PE00088.proved Eq.refl Eq.refl

module r2a_ij6715 where

  proved : X67 • X15 ≈ X15 • X67
  proved = by-assoc-and PE00095.proved Eq.refl Eq.refl

module r2a_ij6723 where

  proved : X67 • X23 ≈ X23 • X67
  proved = by-assoc-and PE00115.proved Eq.refl Eq.refl

module r2a_ij6724 where

  proved : X67 • X24 ≈ X24 • X67
  proved = by-assoc-and PE00122.proved Eq.refl Eq.refl

module r2a_ij6725 where

  proved : X67 • X25 ≈ X25 • X67
  proved = by-assoc-and PE00129.proved Eq.refl Eq.refl

module r2a_ij6734 where

  proved : X67 • X34 ≈ X34 • X67
  proved = by-assoc-and PE00149.proved Eq.refl Eq.refl

module r2a_ij6735 where

  proved : X67 • X35 ≈ X35 • X67
  proved = by-assoc-and PE00156.proved Eq.refl Eq.refl

module r2a_ij6745 where

  proved : X67 • X45 ≈ X45 • X67
  proved = by-assoc-and PE00176.proved Eq.refl Eq.refl

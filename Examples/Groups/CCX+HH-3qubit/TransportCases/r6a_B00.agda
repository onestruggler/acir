{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r6a_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K4567 ; M0 ; M4 ; X04 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; cong ; module Eq ; move-product ; refl ; right-unit ; sym ; trans ; under ; ε)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as R083
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as R095
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R101 as R101
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B064 using (module MV02452)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B078 using (module MV03113)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B018 using (module PE00959)
open import Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_B00 using (module r1b_ij4)

module r6a_ij01234567 where

  step0 : X04 • (M4 • M0) ≈ (M0 • M4) • X04
  step0 = by-assoc-and (move-product MV02452.proved MV03113.proved) Eq.refl Eq.refl

  step1 : X04 • M4 • M0 • X04 • M0 • M4 ≈ M0 • M4 • X04 • X04 • M0 • M4
  step1 = by-assoc-and (cong step0 (refl {w = X04 • M0 • M4})) Eq.refl Eq.refl

  step2 : M0 • M4 • X04 • X04 • M0 • M4 ≈ M0 • M4 • M0 • M4
  step2 = by-assoc-and (under (M0 • M4) (M0 • M4) (by-assoc-and {w = X04 • X04} {v = ε} PE00959.proved Eq.refl Eq.refl)) Eq.refl Eq.refl

  step3 : M0 • M4 • M0 • M4 ≈ M0 • M0 • M4 • M4
  step3 = by-assoc-and (under M0 M4 (sym R095.proved)) Eq.refl Eq.refl

  step4 : M0 • M0 • M4 • M4 ≈ ε
  step4 = by-assoc-and (cong R083.proved r1b_ij4.proved) Eq.refl Eq.refl

  step5 : X04 • M4 • M0 • X04 • M0 • M4 ≈ ε
  step5 = trans step1 (trans step2 (trans step3 step4))

  step6 : M0 • M4 • X04 • K4567 • K0123 • X34 • K0123 • K4567 • X04 • M0 • M4 ≈ (K4567 • K0123 • X34 • K0123 • K4567) • (X04 • M4 • M0 • X04 • M0 • M4)
  step6 = by-assoc-and (cong R101.proved (refl {w = X04 • M0 • M4})) Eq.refl Eq.refl

  proved : M0 • M4 • X04 • K4567 • K0123 • X34 • K0123 • K4567 • X04 • M0 • M4 ≈ K4567 • K0123 • X34 • K0123 • K4567
  proved = trans step6 (trans (cong (refl {w = K4567 • K0123 • X34 • K0123 • K4567}) step5) right-unit)

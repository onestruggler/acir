{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02590 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M5 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00024 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00037 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00038 as L3

proved : p (s3 • s2 • s4 • s3) • M3 ≈ M5 • p (s3 • s2 • s4 • s3)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02602 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M6 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00024 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00040 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00044 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00045 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00046 as L5

proved : p (s4 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s4 • s3 • s2 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

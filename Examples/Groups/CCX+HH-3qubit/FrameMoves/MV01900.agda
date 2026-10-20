{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01900 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M4 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00025 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00023 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00015 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00007 as L4

proved : p (s0 • s1 • s2 • s4 • s3) • M4 ≈ M0 • p (s0 • s1 • s2 • s4 • s3)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

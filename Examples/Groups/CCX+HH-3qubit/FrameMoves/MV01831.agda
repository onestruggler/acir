{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01831 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M2 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00004 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00005 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00000 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00008 as L3

proved : p (s1 • s0 • s5 • s4) • M0 ≈ M2 • p (s1 • s0 • s5 • s4)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

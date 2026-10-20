{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01819 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; M6 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00040 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00042 as L2

proved : p (s0 • s5 • s4) • M4 ≈ M6 • p (s0 • s5 • s4)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

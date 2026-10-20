{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01816 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00004 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00000 as L1

proved : p (s0 • s4) • M0 ≈ M1 • p (s0 • s4)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

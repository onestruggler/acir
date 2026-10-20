{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01806 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00004 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00005 as L1

proved : p (s5 • s4) • M0 ≈ M0 • p (s5 • s4)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

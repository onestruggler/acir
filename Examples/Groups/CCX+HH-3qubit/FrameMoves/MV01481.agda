{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01481 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X27 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00218 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00222 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00203 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00201 as L4

proved : p (s2 • s4 • s3 • s6 • s5) • X45 ≈ X27 • p (s2 • s4 • s3 • s6 • s5)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

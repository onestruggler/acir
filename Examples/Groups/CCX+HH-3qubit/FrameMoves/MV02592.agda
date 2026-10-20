{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02592 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X16 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00121 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00129 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00133 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00134 as L4

proved : p (s3 • s2 • s5 • s4 • s3) • X13 ≈ X16 • p (s3 • s2 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02596 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X17 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00121 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00129 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00137 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00140 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00141 as L5

proved : p (s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X17 • p (s3 • s2 • s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02437 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; K4567 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00629 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00625 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00620 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00615 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00609 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00588 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00570 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00516 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00481 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00369 as L9

proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0156 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))) Eq.refl Eq.refl

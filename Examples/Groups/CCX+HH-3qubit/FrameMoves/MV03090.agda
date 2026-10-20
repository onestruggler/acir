{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03090 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2345 ; K4567 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00557 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00563 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00566 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00578 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00582 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00600 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00604 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00624 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00627 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00628 as L9

proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K4567 • p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))) Eq.refl Eq.refl

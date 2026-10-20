{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03093 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2345 ; K3456 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00557 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00561 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00571 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00587 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00608 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00607 as L5

proved : p (s0 • s1 • s2 • s3 • s4 • s5) • K2345 ≈ K3456 • p (s0 • s1 • s2 • s3 • s4 • s5)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02866 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00003 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00004 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00005 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00002 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00003 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00001 as L5

proved : p (s1 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M0 • p (s1 • s3 • s2 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

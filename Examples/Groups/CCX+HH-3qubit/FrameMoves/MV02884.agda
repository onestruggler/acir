{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02884 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00003 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00004 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00005 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00006 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00002 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00003 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00004 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00001 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00002 as L8

proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))) Eq.refl Eq.refl

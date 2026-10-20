{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02173 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00040 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00048 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00052 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00053 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00054 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00055 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00044 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00045 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00046 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00047 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00036 as L11
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00037 as L12
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00038 as L13
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00039 as L14
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00028 as L15
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00029 as L16
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00030 as L17

proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M4 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
proved = by-assoc-and (move-compose L17.proved (move-compose L16.proved (move-compose L15.proved (move-compose L14.proved (move-compose L13.proved (move-compose L12.proved (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))))))))) Eq.refl Eq.refl

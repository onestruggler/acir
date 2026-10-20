{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01928 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M4 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00025 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00026 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00027 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00023 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00017 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00018 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00019 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00015 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00009 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00010 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00011 as L11
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00007 as L12
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00001 as L13

proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L13.proved (move-compose L12.proved (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))))) Eq.refl Eq.refl

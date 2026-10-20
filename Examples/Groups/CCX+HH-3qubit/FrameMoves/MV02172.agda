{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02172 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K2567 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00246 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00248 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00251 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00257 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00263 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00264 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00288 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00306 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00318 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00320 as L11
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00383 as L12
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00420 as L13
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00438 as L14
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00440 as L15
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00551 as L16

proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K2567 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
proved = by-assoc-and (move-compose L16.proved (move-compose L15.proved (move-compose L14.proved (move-compose L13.proved (move-compose L12.proved (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))))))))))) Eq.refl Eq.refl

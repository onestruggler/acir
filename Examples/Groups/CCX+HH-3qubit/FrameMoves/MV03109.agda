{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03109 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K1346 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00252 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00253 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00251 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00257 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00260 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00261 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00259 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00282 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00297 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00356 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00392 as L10

proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K1346 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))))) Eq.refl Eq.refl

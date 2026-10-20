{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01614 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X37 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00218 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00223 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00235 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00236 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00221 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00222 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00200 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00199 as L8

proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X37 • p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))) Eq.refl Eq.refl

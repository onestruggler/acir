{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01416 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X24 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00218 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00223 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00235 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00236 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00224 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00225 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00214 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00215 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00196 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00197 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00186 as L11
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00187 as L12
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00161 as L13
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00162 as L14
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00151 as L15

proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X24 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L15.proved (move-compose L14.proved (move-compose L13.proved (move-compose L12.proved (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))))))) Eq.refl Eq.refl

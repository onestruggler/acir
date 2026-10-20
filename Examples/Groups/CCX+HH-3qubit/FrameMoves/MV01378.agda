{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01378 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0457 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00246 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00251 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00257 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00263 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00264 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00288 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00306 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00314 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00376 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00413 as L11

proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0457 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
proved = by-assoc-and (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))) Eq.refl Eq.refl

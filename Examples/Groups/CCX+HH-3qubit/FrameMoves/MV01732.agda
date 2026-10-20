{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01732 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K1234 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00246 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00249 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00269 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00325 as L5

proved : p (s0 • s1 • s2 • s3 • s4 • s5) • K0123 ≈ K1234 • p (s0 • s1 • s2 • s3 • s4 • s5)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

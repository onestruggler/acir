{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02263 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0234 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00246 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00249 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00269 as L4

proved : p (s1 • s2 • s3 • s5 • s4) • K0123 ≈ K0234 • p (s1 • s2 • s3 • s5 • s4)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

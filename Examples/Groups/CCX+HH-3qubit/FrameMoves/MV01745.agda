{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01745 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X45 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00218 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00223 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00237 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00242 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00243 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00244 as L6

proved : p (s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X57 • p (s5 • s4 • s3 • s5 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

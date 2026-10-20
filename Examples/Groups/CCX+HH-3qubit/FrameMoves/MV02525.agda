{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02525 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; K0267 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00344 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00365 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00379 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00385 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00384 as L4

proved : p (s3 • s4 • s5 • s4 • s3) • K0237 ≈ K0267 • p (s3 • s4 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

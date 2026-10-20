{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03053 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; K1467 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00500 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00507 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00511 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00525 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00530 as L4

proved : p (s3 • s5 • s4 • s6 • s5) • K1345 ≈ K1467 • p (s3 • s5 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

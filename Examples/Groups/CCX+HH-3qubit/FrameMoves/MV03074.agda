{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03074 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; K2456 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00500 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00505 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00517 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00535 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00534 as L4

proved : p (s1 • s2 • s3 • s4 • s5) • K1345 ≈ K2456 • p (s1 • s2 • s3 • s4 • s5)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

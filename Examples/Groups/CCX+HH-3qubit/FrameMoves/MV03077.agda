{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03077 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; K2457 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00500 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00507 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00511 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00523 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00540 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00539 as L5

proved : p (s1 • s2 • s3 • s4 • s6 • s5) • K1345 ≈ K2457 • p (s1 • s2 • s3 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

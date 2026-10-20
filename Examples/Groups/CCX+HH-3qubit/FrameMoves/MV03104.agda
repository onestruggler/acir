{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03104 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; K2567 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00500 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00507 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00511 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00525 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00530 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00548 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00552 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00553 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00551 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00602 as L9

proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K2567 • p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))) Eq.refl Eq.refl

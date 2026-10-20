{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02501 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; K0567 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00320 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00383 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00420 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00438 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00443 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00442 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00441 as L6

proved : p (s1 • s2 • s3 • s4 • s3 • s2 • s1) • K0167 ≈ K0567 • p (s1 • s2 • s3 • s4 • s3 • s2 • s1)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

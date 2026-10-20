{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02613 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M2 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00010 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00009 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00008 as L2

proved : p (s1 • s2 • s3) • M1 ≈ M2 • p (s1 • s2 • s3)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

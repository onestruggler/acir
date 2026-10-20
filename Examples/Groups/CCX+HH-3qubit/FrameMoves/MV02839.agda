{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02839 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00003 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00004 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00002 as L2

proved : p (s2 • s4 • s3) • M0 ≈ M0 • p (s2 • s4 • s3)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

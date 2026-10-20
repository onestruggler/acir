{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02589 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00010 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00011 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00009 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00010 as L3

proved : p (s3 • s2 • s4 • s3) • M1 ≈ M1 • p (s3 • s2 • s4 • s3)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

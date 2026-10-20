{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02573 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00010 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00009 as L1

proved : p (s2 • s3) • M1 ≈ M1 • p (s2 • s3)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

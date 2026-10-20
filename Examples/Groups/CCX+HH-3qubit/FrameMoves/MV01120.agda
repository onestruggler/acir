{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01120 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00209 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00187 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00159 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00124 as L3

proved : p (s0 • s1 • s2 • s3) • X45 ≈ X05 • p (s0 • s1 • s2 • s3)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

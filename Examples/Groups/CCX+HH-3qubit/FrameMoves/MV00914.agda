{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00914 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00118 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00153 as L3

proved : p (s2 • s1 • s3 • s2) • X12 ≈ X34 • p (s2 • s1 • s3 • s2)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

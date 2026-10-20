{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00807 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00002 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00003 as L1

proved : p (s3 • s2) • M0 ≈ M0 • p (s3 • s2)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01815 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M4 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00021 as L1

proved : p (s0 • s3) • M4 ≈ M3 • p (s0 • s3)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

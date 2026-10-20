{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01564 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X36 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00215 as L1

proved : p (s3 • s5) • X45 ≈ X36 • p (s3 • s5)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

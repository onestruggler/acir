{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02559 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00058 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00059 as L1

proved : p (s4 • s3) • X01 ≈ X01 • p (s4 • s3)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01450 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0134 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00249 as L2

proved : p (s2 • s3 • s5) • K0123 ≈ K0134 • p (s2 • s3 • s5)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

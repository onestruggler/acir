{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02497 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; K0367 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00320 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00383 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00418 as L2

proved : p (s1 • s2 • s1) • K0167 ≈ K0367 • p (s1 • s2 • s1)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

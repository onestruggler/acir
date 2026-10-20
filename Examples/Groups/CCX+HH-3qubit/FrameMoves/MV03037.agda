{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03037 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00252 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00253 as L1

proved : p (s6 • s5) • K0124 ≈ K0124 • p (s6 • s5)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

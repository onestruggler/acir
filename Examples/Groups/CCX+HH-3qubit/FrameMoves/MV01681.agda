{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01681 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X45 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00218 as L1

proved : p (s6 • s5) • X45 ≈ X47 • p (s6 • s5)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

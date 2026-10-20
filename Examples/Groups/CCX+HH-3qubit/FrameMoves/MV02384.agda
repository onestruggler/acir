{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02384 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3456 ; K4567 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00629 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00625 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00620 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00615 as L3

proved : p (s6 • s5 • s4 • s3) • K4567 ≈ K3456 • p (s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

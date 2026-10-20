{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02530 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; K1267 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00460 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00478 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00490 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00495 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00494 as L4

proved : p (s3 • s4 • s5 • s4 • s3) • K1237 ≈ K1267 • p (s3 • s4 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

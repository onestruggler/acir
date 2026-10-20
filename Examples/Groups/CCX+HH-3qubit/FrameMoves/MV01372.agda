{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01372 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X23 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00209 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00189 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00183 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00181 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00154 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00148 as L5

proved : p (s4 • s3 • s2 • s5 • s4 • s3) • X45 ≈ X23 • p (s4 • s3 • s2 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

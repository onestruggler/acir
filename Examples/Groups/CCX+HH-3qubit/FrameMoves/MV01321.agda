{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01321 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X16 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00215 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00196 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00194 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00168 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00166 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00133 as L6

proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s5) • X45 ≈ X16 • p (s2 • s1 • s3 • s2 • s4 • s3 • s5)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01283 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X15 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00215 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00196 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00197 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00191 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00187 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00159 as L6

proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X15 • p (s1 • s2 • s6 • s5 • s4 • s3 • s5)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01546 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X35 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00216 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00229 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00230 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00217 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00208 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00209 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00186 as L7

proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X35 • p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
proved = by-assoc-and (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))) Eq.refl Eq.refl

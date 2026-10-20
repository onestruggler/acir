{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01327 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X16 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00218 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00222 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00203 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00204 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00205 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00194 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00168 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00169 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00166 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00133 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00134 as L11

proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X16 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
proved = by-assoc-and (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))) Eq.refl Eq.refl

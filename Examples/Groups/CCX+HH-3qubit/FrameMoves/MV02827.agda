{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02827 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00058 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00059 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00060 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00061 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00057 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00058 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00059 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00060 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00056 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00064 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00072 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00080 as L11
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00083 as L12
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00125 as L13
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00160 as L14
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00188 as L15

proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X45 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L15.proved (move-compose L14.proved (move-compose L13.proved (move-compose L12.proved (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))))))) Eq.refl Eq.refl

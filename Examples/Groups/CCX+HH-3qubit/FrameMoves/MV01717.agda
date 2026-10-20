{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01717 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X45 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00216 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00229 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00228 as L3

proved : p (s2 • s3 • s4 • s5) • X45 ≈ X56 • p (s2 • s3 • s4 • s5)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

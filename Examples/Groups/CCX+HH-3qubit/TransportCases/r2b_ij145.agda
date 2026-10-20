{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00812 as MV00812
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00813 as MV00813
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X14 • M5 ≈ M5 • X14
proved = GL.•-cancelʳ {g = X14 • M5} {g' = M5 • X14} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00812.proved (MV00813.proved))) (trans (cong refl Base.proved) (move-product MV00813.proved (MV00812.proved))))

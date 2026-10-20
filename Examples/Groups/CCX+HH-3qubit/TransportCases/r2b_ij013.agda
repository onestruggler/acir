{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij013 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00630 as MV00630
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00710 as MV00710
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X01 • M3 ≈ M3 • X01
proved = GL.•-cancelʳ {g = X01 • M3} {g' = M3 • X01} {h = p (s2 • s1 • s0)}
  (trans (sym (move-product MV00710.proved (MV00630.proved))) (trans (cong refl Base.proved) (move-product MV00630.proved (MV00710.proved))))

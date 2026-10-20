{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij163 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00834 as MV00834
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00835 as MV00835
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X16 • M3 ≈ M3 • X16
proved = GL.•-cancelʳ {g = X16 • M3} {g' = M3 • X16} {h = p (s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00834.proved (MV00835.proved))) (trans (cong refl Base.proved) (move-product MV00835.proved (MV00834.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij074 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X07 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00779 as MV00779
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00780 as MV00780
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X07 • M4 ≈ M4 • X07
proved = GL.•-cancelʳ {g = X07 • M4} {g' = M4 • X07} {h = p (s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00779.proved (MV00780.proved))) (trans (cong refl Base.proved) (move-product MV00780.proved (MV00779.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00886 as MV00886
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00887 as MV00887
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X25 • M6 ≈ M6 • X25
proved = GL.•-cancelʳ {g = X25 • M6} {g' = M6 • X25} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00886.proved (MV00887.proved))) (trans (cong refl Base.proved) (move-product MV00887.proved (MV00886.proved))))

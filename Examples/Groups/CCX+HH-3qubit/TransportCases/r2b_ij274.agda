{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij274 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00908 as MV00908
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00909 as MV00909
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X27 • M4 ≈ M4 • X27
proved = GL.•-cancelʳ {g = X27 • M4} {g' = M4 • X27} {h = p (s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00908.proved (MV00909.proved))) (trans (cong refl Base.proved) (move-product MV00909.proved (MV00908.proved))))

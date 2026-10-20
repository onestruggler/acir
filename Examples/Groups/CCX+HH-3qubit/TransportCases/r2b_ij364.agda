{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij364 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00944 as MV00944
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00945 as MV00945
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X36 • M4 ≈ M4 • X36
proved = GL.•-cancelʳ {g = X36 • M4} {g' = M4 • X36} {h = p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00944.proved (MV00945.proved))) (trans (cong refl Base.proved) (move-product MV00945.proved (MV00944.proved))))

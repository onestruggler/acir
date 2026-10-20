{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij254 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00884 as MV00884
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00885 as MV00885
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X25 • M4 ≈ M4 • X25
proved = GL.•-cancelʳ {g = X25 • M4} {g' = M4 • X25} {h = p (s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00884.proved (MV00885.proved))) (trans (cong refl Base.proved) (move-product MV00885.proved (MV00884.proved))))

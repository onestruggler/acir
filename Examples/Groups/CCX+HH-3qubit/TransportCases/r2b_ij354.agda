{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij354 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00932 as MV00932
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00933 as MV00933
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X35 • M4 ≈ M4 • X35
proved = GL.•-cancelʳ {g = X35 • M4} {g' = M4 • X35} {h = p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00932.proved (MV00933.proved))) (trans (cong refl Base.proved) (move-product MV00933.proved (MV00932.proved))))

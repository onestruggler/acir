{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00934 as MV00934
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00935 as MV00935
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X35 • M6 ≈ M6 • X35
proved = GL.•-cancelʳ {g = X35 • M6} {g' = M6 • X35} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00934.proved (MV00935.proved))) (trans (cong refl Base.proved) (move-product MV00935.proved (MV00934.proved))))

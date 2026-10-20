{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij360 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00938 as MV00938
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00939 as MV00939
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X36 • M0 ≈ M0 • X36
proved = GL.•-cancelʳ {g = X36 • M0} {g' = M0 • X36} {h = p (s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00938.proved (MV00939.proved))) (trans (cong refl Base.proved) (move-product MV00939.proved (MV00938.proved))))

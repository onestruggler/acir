{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00209 as MV00209
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as MV00245
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K0124 ≈ K0124 • X35
proved = GL.•-cancelʳ {g = X35 • K0124} {g' = K0124 • X35} {h = p (s3)}
  (trans (sym (move-product MV00209.proved (MV00245.proved))) (trans (cong refl Base.proved) (move-product MV00245.proved (MV00209.proved))))

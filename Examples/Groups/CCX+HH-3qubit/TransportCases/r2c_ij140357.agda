{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij140357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0357 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01264 as MV01264
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01265 as MV01265
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X14 • K0357 ≈ K0357 • X14
proved = GL.•-cancelʳ {g = X14 • K0357} {g' = K0357 • X14} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01264.proved (MV01265.proved))) (trans (cong refl Base.proved) (move-product MV01265.proved (MV01264.proved))))

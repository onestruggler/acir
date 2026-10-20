{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij162457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2457 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01335 as MV01335
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01336 as MV01336
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K2457 ≈ K2457 • X16
proved = GL.•-cancelʳ {g = X16 • K2457} {g' = K2457 • X16} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01335.proved (MV01336.proved))) (trans (cong refl Base.proved) (move-product MV01336.proved (MV01335.proved))))

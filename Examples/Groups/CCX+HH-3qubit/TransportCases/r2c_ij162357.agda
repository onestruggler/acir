{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij162357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2357 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01333 as MV01333
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01334 as MV01334
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K2357 ≈ K2357 • X16
proved = GL.•-cancelʳ {g = X16 • K2357} {g' = K2357 • X16} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01333.proved (MV01334.proved))) (trans (cong refl Base.proved) (move-product MV01334.proved (MV01333.proved))))

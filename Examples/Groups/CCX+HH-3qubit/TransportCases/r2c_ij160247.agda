{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0247 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01317 as MV01317
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01318 as MV01318
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K0247 ≈ K0247 • X16
proved = GL.•-cancelʳ {g = X16 • K0247} {g' = K0247 • X16} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01317.proved (MV01318.proved))) (trans (cong refl Base.proved) (move-product MV01318.proved (MV01317.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01315 as MV01315
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01316 as MV01316
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K0245 ≈ K0245 • X16
proved = GL.•-cancelʳ {g = X16 • K0245} {g' = K0245 • X16} {h = p (s1 • s3 • s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01315.proved (MV01316.proved))) (trans (cong refl Base.proved) (move-product MV01316.proved (MV01315.proved))))

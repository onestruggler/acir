{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01309 as MV01309
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01310 as MV01310
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K0234 ≈ K0234 • X16
proved = GL.•-cancelʳ {g = X16 • K0234} {g' = K0234 • X16} {h = p (s1 • s2 • s3 • s5)}
  (trans (sym (move-product MV01309.proved (MV01310.proved))) (trans (cong refl Base.proved) (move-product MV01310.proved (MV01309.proved))))

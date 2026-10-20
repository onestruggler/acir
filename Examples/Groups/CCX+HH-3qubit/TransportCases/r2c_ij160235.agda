{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01311 as MV01311
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01312 as MV01312
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K0235 ≈ K0235 • X16
proved = GL.•-cancelʳ {g = X16 • K0235} {g' = K0235 • X16} {h = p (s1 • s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01311.proved (MV01312.proved))) (trans (cong refl Base.proved) (move-product MV01312.proved (MV01311.proved))))

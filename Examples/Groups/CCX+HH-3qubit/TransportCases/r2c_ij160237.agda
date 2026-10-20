{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01313 as MV01313
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01314 as MV01314
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K0237 ≈ K0237 • X16
proved = GL.•-cancelʳ {g = X16 • K0237} {g' = K0237 • X16} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01313.proved (MV01314.proved))) (trans (cong refl Base.proved) (move-product MV01314.proved (MV01313.proved))))

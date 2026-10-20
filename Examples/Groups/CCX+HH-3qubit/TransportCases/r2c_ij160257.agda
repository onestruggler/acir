{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01319 as MV01319
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01320 as MV01320
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K0257 ≈ K0257 • X16
proved = GL.•-cancelʳ {g = X16 • K0257} {g' = K0257 • X16} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01319.proved (MV01320.proved))) (trans (cong refl Base.proved) (move-product MV01320.proved (MV01319.proved))))

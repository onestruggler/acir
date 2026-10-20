{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij051237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01123 as MV01123
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01124 as MV01124
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X05 • K1237 ≈ K1237 • X05
proved = GL.•-cancelʳ {g = X05 • K1237} {g' = K1237 • X05} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01123.proved (MV01124.proved))) (trans (cong refl Base.proved) (move-product MV01124.proved (MV01123.proved))))

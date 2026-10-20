{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij071234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1234 ; X07 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01179 as MV01179
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01180 as MV01180
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X07 • K1234 ≈ K1234 • X07
proved = GL.•-cancelʳ {g = X07 • K1234} {g' = K1234 • X07} {h = p (s0 • s1 • s2 • s3 • s6 • s5)}
  (trans (sym (move-product MV01179.proved (MV01180.proved))) (trans (cong refl Base.proved) (move-product MV01180.proved (MV01179.proved))))

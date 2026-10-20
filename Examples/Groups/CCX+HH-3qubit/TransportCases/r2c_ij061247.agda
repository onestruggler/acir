{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij061247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01157 as MV01157
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01158 as MV01158
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X06 • K1247 ≈ K1247 • X06
proved = GL.•-cancelʳ {g = X06 • K1247} {g' = K1247 • X06} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01157.proved (MV01158.proved))) (trans (cong refl Base.proved) (move-product MV01158.proved (MV01157.proved))))

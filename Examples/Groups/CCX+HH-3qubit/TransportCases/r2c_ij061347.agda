{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij061347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1347 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01163 as MV01163
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01164 as MV01164
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X06 • K1347 ≈ K1347 • X06
proved = GL.•-cancelʳ {g = X06 • K1347} {g' = K1347 • X06} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01163.proved (MV01164.proved))) (trans (cong refl Base.proved) (move-product MV01164.proved (MV01163.proved))))

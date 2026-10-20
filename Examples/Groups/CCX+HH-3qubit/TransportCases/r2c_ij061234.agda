{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij061234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1234 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01149 as MV01149
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01150 as MV01150
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X06 • K1234 ≈ K1234 • X06
proved = GL.•-cancelʳ {g = X06 • K1234} {g' = K1234 • X06} {h = p (s0 • s1 • s2 • s3 • s5)}
  (trans (sym (move-product MV01149.proved (MV01150.proved))) (trans (cong refl Base.proved) (move-product MV01150.proved (MV01149.proved))))

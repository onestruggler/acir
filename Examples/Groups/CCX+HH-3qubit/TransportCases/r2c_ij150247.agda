{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0247 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01287 as MV01287
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01288 as MV01288
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X15 • K0247 ≈ K0247 • X15
proved = GL.•-cancelʳ {g = X15 • K0247} {g' = K0247 • X15} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01287.proved (MV01288.proved))) (trans (cong refl Base.proved) (move-product MV01288.proved (MV01287.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij051234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1234 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00675 as MV00675
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01120 as MV01120
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X05 • K1234 ≈ K1234 • X05
proved = GL.•-cancelʳ {g = X05 • K1234} {g' = K1234 • X05} {h = p (s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV01120.proved (MV00675.proved))) (trans (cong refl Base.proved) (move-product MV00675.proved (MV01120.proved))))

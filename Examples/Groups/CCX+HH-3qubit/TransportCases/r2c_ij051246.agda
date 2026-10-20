{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij051246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01125 as MV01125
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01126 as MV01126
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X05 • K1246 ≈ K1246 • X05
proved = GL.•-cancelʳ {g = X05 • K1246} {g' = K1246 • X05} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01125.proved (MV01126.proved))) (trans (cong refl Base.proved) (move-product MV01126.proved (MV01125.proved))))

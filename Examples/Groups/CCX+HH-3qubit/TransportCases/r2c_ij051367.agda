{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij051367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1367 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01135 as MV01135
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01136 as MV01136
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X05 • K1367 ≈ K1367 • X05
proved = GL.•-cancelʳ {g = X05 • K1367} {g' = K1367 • X05} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01135.proved (MV01136.proved))) (trans (cong refl Base.proved) (move-product MV01136.proved (MV01135.proved))))

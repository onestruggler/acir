{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij051346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1346 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01131 as MV01131
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01132 as MV01132
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X05 • K1346 ≈ K1346 • X05
proved = GL.•-cancelʳ {g = X05 • K1346} {g' = K1346 • X05} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01131.proved (MV01132.proved))) (trans (cong refl Base.proved) (move-product MV01132.proved (MV01131.proved))))

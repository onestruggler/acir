{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij051236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1236 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01121 as MV01121
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01122 as MV01122
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X05 • K1236 ≈ K1236 • X05
proved = GL.•-cancelʳ {g = X05 • K1236} {g' = K1236 • X05} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01121.proved (MV01122.proved))) (trans (cong refl Base.proved) (move-product MV01122.proved (MV01121.proved))))

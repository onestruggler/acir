{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij071246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; X07 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01187 as MV01187
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01188 as MV01188
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X07 • K1246 ≈ K1246 • X07
proved = GL.•-cancelʳ {g = X07 • K1246} {g' = K1246 • X07} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01187.proved (MV01188.proved))) (trans (cong refl Base.proved) (move-product MV01188.proved (MV01187.proved))))

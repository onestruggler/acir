{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01283 as MV01283
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01284 as MV01284
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X15 • K0237 ≈ K0237 • X15
proved = GL.•-cancelʳ {g = X15 • K0237} {g' = K0237 • X15} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01283.proved (MV01284.proved))) (trans (cong refl Base.proved) (move-product MV01284.proved (MV01283.proved))))

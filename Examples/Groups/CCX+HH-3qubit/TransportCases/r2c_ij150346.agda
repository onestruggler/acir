{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01291 as MV01291
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01292 as MV01292
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X15 • K0346 ≈ K0346 • X15
proved = GL.•-cancelʳ {g = X15 • K0346} {g' = K0346 • X15} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01291.proved (MV01292.proved))) (trans (cong refl Base.proved) (move-product MV01292.proved (MV01291.proved))))

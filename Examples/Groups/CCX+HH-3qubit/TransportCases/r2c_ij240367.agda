{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01406 as MV01406
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01407 as MV01407
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K0367 ≈ K0367 • X24
proved = GL.•-cancelʳ {g = X24 • K0367} {g' = K0367 • X24} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01406.proved (MV01407.proved))) (trans (cong refl Base.proved) (move-product MV01407.proved (MV01406.proved))))

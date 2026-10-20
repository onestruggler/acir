{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0357 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01404 as MV01404
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01405 as MV01405
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K0357 ≈ K0357 • X24
proved = GL.•-cancelʳ {g = X24 • K0357} {g' = K0357 • X24} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01404.proved (MV01405.proved))) (trans (cong refl Base.proved) (move-product MV01405.proved (MV01404.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij241567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1567 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01416 as MV01416
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01417 as MV01417
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K1567 ≈ K1567 • X24
proved = GL.•-cancelʳ {g = X24 • K1567} {g' = K1567 • X24} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01416.proved (MV01417.proved))) (trans (cong refl Base.proved) (move-product MV01417.proved (MV01416.proved))))

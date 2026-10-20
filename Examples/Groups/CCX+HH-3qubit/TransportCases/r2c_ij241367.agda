{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij241367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1367 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01414 as MV01414
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01415 as MV01415
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K1367 ≈ K1367 • X24
proved = GL.•-cancelʳ {g = X24 • K1367} {g' = K1367 • X24} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01414.proved (MV01415.proved))) (trans (cong refl Base.proved) (move-product MV01415.proved (MV01414.proved))))

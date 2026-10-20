{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij241356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1356 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01410 as MV01410
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01411 as MV01411
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K1356 ≈ K1356 • X24
proved = GL.•-cancelʳ {g = X24 • K1356} {g' = K1356 • X24} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01410.proved (MV01411.proved))) (trans (cong refl Base.proved) (move-product MV01411.proved (MV01410.proved))))

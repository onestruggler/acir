{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01489 as MV01489
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01490 as MV01490
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K0156 ≈ K0156 • X27
proved = GL.•-cancelʳ {g = X27 • K0156} {g' = K0156 • X27} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01489.proved (MV01490.proved))) (trans (cong refl Base.proved) (move-product MV01490.proved (MV01489.proved))))

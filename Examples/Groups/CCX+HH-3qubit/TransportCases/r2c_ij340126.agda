{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij340126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00643 as MV00643
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01510 as MV01510
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K0126 ≈ K0126 • X34
proved = GL.•-cancelʳ {g = X34 • K0126} {g' = K0126 • X34} {h = p (s5 • s4 • s3)}
  (trans (sym (move-product MV01510.proved (MV00643.proved))) (trans (cong refl Base.proved) (move-product MV00643.proved (MV01510.proved))))

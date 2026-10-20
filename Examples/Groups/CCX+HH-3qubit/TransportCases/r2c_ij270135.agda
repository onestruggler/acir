{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01481 as MV01481
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01482 as MV01482
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K0135 ≈ K0135 • X27
proved = GL.•-cancelʳ {g = X27 • K0135} {g' = K0135 • X27} {h = p (s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01481.proved (MV01482.proved))) (trans (cong refl Base.proved) (move-product MV01482.proved (MV01481.proved))))

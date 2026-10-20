{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01479 as MV01479
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01480 as MV01480
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K0134 ≈ K0134 • X27
proved = GL.•-cancelʳ {g = X27 • K0134} {g' = K0134 • X27} {h = p (s2 • s3 • s6 • s5)}
  (trans (sym (move-product MV01479.proved (MV01480.proved))) (trans (cong refl Base.proved) (move-product MV01480.proved (MV01479.proved))))

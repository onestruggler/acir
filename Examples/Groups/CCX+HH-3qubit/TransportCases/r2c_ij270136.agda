{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01483 as MV01483
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01484 as MV01484
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K0136 ≈ K0136 • X27
proved = GL.•-cancelʳ {g = X27 • K0136} {g' = K0136 • X27} {h = p (s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01483.proved (MV01484.proved))) (trans (cong refl Base.proved) (move-product MV01484.proved (MV01483.proved))))

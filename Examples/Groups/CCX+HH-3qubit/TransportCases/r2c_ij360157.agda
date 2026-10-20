{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01574 as MV01574
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01575 as MV01575
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K0157 ≈ K0157 • X36
proved = GL.•-cancelʳ {g = X36 • K0157} {g' = K0157 • X36} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01574.proved (MV01575.proved))) (trans (cong refl Base.proved) (move-product MV01575.proved (MV01574.proved))))

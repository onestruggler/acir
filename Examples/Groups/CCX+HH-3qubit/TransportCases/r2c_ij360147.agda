{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01572 as MV01572
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01573 as MV01573
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K0147 ≈ K0147 • X36
proved = GL.•-cancelʳ {g = X36 • K0147} {g' = K0147 • X36} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01572.proved (MV01573.proved))) (trans (cong refl Base.proved) (move-product MV01573.proved (MV01572.proved))))

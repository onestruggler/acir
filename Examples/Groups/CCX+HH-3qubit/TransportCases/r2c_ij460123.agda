{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij460123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as MV00210
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as MV00247
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X46 • K0123 ≈ K0123 • X46
proved = GL.•-cancelʳ {g = X46 • K0123} {g' = K0123 • X46} {h = p (s5)}
  (trans (sym (move-product MV00210.proved (MV00247.proved))) (trans (cong refl Base.proved) (move-product MV00247.proved (MV00210.proved))))

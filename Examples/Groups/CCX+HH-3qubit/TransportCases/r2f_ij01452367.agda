{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01452367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; K2367 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00649 as MV00649
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02389 as MV02389
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0145 • K2367 ≈ K2367 • K0145
proved = GL.•-cancelʳ {g = K0145 • K2367} {g' = K2367 • K0145} {h = p (s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00649.proved (MV02389.proved))) (trans (cong refl Base.proved) (move-product MV02389.proved (MV00649.proved))))

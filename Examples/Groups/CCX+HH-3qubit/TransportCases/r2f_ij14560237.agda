{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij14560237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; K1456 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00691 as MV00691
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02431 as MV02431
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1456 • K0237 ≈ K0237 • K1456
proved = GL.•-cancelʳ {g = K1456 • K0237} {g' = K0237 • K1456} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00691.proved (MV02431.proved))) (trans (cong refl Base.proved) (move-product MV02431.proved (MV00691.proved))))

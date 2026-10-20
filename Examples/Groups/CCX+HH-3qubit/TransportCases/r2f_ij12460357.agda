{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12460357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0357 ; K1246 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00680 as MV00680
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02420 as MV02420
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1246 • K0357 ≈ K0357 • K1246
proved = GL.•-cancelʳ {g = K1246 • K0357} {g' = K0357 • K1246} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00680.proved (MV02420.proved))) (trans (cong refl Base.proved) (move-product MV02420.proved (MV00680.proved))))

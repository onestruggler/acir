{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij13560247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0247 ; K1356 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00688 as MV00688
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02428 as MV02428
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1356 • K0247 ≈ K0247 • K1356
proved = GL.•-cancelʳ {g = K1356 • K0247} {g' = K0247 • K1356} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00688.proved (MV02428.proved))) (trans (cong refl Base.proved) (move-product MV02428.proved (MV00688.proved))))

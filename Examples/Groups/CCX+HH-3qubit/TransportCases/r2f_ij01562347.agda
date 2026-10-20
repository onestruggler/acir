{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01562347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; K2347 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00652 as MV00652
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02392 as MV02392
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0156 • K2347 ≈ K2347 • K0156
proved = GL.•-cancelʳ {g = K0156 • K2347} {g' = K2347 • K0156} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00652.proved (MV02392.proved))) (trans (cong refl Base.proved) (move-product MV02392.proved (MV00652.proved))))

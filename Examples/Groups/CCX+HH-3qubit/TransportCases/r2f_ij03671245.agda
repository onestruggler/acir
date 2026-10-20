{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij03671245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; K1245 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00670 as MV00670
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02410 as MV02410
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0367 • K1245 ≈ K1245 • K0367
proved = GL.•-cancelʳ {g = K0367 • K1245} {g' = K1245 • K0367} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00670.proved (MV02410.proved))) (trans (cong refl Base.proved) (move-product MV02410.proved (MV00670.proved))))

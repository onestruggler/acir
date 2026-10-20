{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02209 as MV02209
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02210 as MV02210
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0367 ≈ K0367 • M5
proved = GL.•-cancelʳ {g = M5 • K0367} {g' = K0367 • M5} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02209.proved (MV02210.proved))) (trans (cong refl Base.proved) (move-product MV02210.proved (MV02209.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij51367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1367 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02229 as MV02229
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02230 as MV02230
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K1367 ≈ K1367 • M5
proved = GL.•-cancelʳ {g = M5 • K1367} {g' = K1367 • M5} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02229.proved (MV02230.proved))) (trans (cong refl Base.proved) (move-product MV02230.proved (MV02229.proved))))

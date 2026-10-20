{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0236 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02195 as MV02195
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02196 as MV02196
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0236 ≈ K0236 • M5
proved = GL.•-cancelʳ {g = M5 • K0236} {g' = K0236 • M5} {h = p (s1 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02195.proved (MV02196.proved))) (trans (cong refl Base.proved) (move-product MV02196.proved (MV02195.proved))))

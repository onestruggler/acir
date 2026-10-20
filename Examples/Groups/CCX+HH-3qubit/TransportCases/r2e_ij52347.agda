{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij52347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2347 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02235 as MV02235
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02236 as MV02236
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K2347 ≈ K2347 • M5
proved = GL.•-cancelʳ {g = M5 • K2347} {g' = K2347 • M5} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02235.proved (MV02236.proved))) (trans (cong refl Base.proved) (move-product MV02236.proved (MV02235.proved))))

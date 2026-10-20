{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij31567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1567 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02095 as MV02095
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02096 as MV02096
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K1567 ≈ K1567 • M3
proved = GL.•-cancelʳ {g = M3 • K1567} {g' = K1567 • M3} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02095.proved (MV02096.proved))) (trans (cong refl Base.proved) (move-product MV02096.proved (MV02095.proved))))

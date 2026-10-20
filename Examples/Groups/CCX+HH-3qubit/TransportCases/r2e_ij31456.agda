{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij31456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1456 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02089 as MV02089
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02090 as MV02090
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K1456 ≈ K1456 • M3
proved = GL.•-cancelʳ {g = M3 • K1456} {g' = K1456 • M3} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02089.proved (MV02090.proved))) (trans (cong refl Base.proved) (move-product MV02090.proved (MV02089.proved))))

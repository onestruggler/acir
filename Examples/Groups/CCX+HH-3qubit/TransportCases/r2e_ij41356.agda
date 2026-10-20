{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij41356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1356 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02157 as MV02157
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02158 as MV02158
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K1356 ≈ K1356 • M4
proved = GL.•-cancelʳ {g = M4 • K1356} {g' = K1356 • M4} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02157.proved (MV02158.proved))) (trans (cong refl Base.proved) (move-product MV02158.proved (MV02157.proved))))

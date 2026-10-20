{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij41237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02149 as MV02149
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02150 as MV02150
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K1237 ≈ K1237 • M4
proved = GL.•-cancelʳ {g = M4 • K1237} {g' = K1237 • M4} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02149.proved (MV02150.proved))) (trans (cong refl Base.proved) (move-product MV02150.proved (MV02149.proved))))

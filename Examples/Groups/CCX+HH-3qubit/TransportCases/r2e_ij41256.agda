{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij41256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1256 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02151 as MV02151
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02152 as MV02152
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K1256 ≈ K1256 • M4
proved = GL.•-cancelʳ {g = M4 • K1256} {g' = K1256 • M4} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02151.proved (MV02152.proved))) (trans (cong refl Base.proved) (move-product MV02152.proved (MV02151.proved))))

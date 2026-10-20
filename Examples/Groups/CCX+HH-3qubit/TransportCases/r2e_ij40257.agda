{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02133 as MV02133
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02134 as MV02134
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0257 ≈ K0257 • M4
proved = GL.•-cancelʳ {g = M4 • K0257} {g' = K0257 • M4} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02133.proved (MV02134.proved))) (trans (cong refl Base.proved) (move-product MV02134.proved (MV02133.proved))))

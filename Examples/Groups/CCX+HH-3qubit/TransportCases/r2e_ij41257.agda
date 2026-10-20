{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij41257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1257 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02153 as MV02153
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02154 as MV02154
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K1257 ≈ K1257 • M4
proved = GL.•-cancelʳ {g = M4 • K1257} {g' = K1257 • M4} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02153.proved (MV02154.proved))) (trans (cong refl Base.proved) (move-product MV02154.proved (MV02153.proved))))

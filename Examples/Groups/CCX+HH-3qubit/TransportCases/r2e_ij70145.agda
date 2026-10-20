{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02325 as MV02325
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02326 as MV02326
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K0145 ≈ K0145 • M7
proved = GL.•-cancelʳ {g = M7 • K0145} {g' = K0145 • M7} {h = p (s3 • s2 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02325.proved (MV02326.proved))) (trans (cong refl Base.proved) (move-product MV02326.proved (MV02325.proved))))

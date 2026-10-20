{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02319 as MV02319
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02320 as MV02320
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K0134 ≈ K0134 • M7
proved = GL.•-cancelʳ {g = M7 • K0134} {g' = K0134 • M7} {h = p (s2 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02319.proved (MV02320.proved))) (trans (cong refl Base.proved) (move-product MV02320.proved (MV02319.proved))))

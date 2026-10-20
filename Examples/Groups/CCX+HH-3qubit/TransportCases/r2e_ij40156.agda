{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02119 as MV02119
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02120 as MV02120
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0156 ≈ K0156 • M4
proved = GL.•-cancelʳ {g = M4 • K0156} {g' = K0156 • M4} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02119.proved (MV02120.proved))) (trans (cong refl Base.proved) (move-product MV02120.proved (MV02119.proved))))

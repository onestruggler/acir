{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02177 as MV02177
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02178 as MV02178
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0126 ≈ K0126 • M5
proved = GL.•-cancelʳ {g = M5 • K0126} {g' = K0126 • M5} {h = p (s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02177.proved (MV02178.proved))) (trans (cong refl Base.proved) (move-product MV02178.proved (MV02177.proved))))

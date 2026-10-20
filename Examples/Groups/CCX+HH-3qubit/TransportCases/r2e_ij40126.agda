{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02109 as MV02109
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02110 as MV02110
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0126 ≈ K0126 • M4
proved = GL.•-cancelʳ {g = M4 • K0126} {g' = K0126 • M4} {h = p (s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02109.proved (MV02110.proved))) (trans (cong refl Base.proved) (move-product MV02110.proved (MV02109.proved))))

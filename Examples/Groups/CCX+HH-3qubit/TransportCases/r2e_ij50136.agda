{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02183 as MV02183
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02184 as MV02184
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0136 ≈ K0136 • M5
proved = GL.•-cancelʳ {g = M5 • K0136} {g' = K0136 • M5} {h = p (s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02183.proved (MV02184.proved))) (trans (cong refl Base.proved) (move-product MV02184.proved (MV02183.proved))))

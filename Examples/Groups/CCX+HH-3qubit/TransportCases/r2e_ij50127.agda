{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02179 as MV02179
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02180 as MV02180
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0127 ≈ K0127 • M5
proved = GL.•-cancelʳ {g = M5 • K0127} {g' = K0127 • M5} {h = p (s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02179.proved (MV02180.proved))) (trans (cong refl Base.proved) (move-product MV02180.proved (MV02179.proved))))

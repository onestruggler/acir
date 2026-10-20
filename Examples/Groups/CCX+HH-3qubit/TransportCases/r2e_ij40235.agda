{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02125 as MV02125
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02126 as MV02126
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0235 ≈ K0235 • M4
proved = GL.•-cancelʳ {g = M4 • K0235} {g' = K0235 • M4} {h = p (s1 • s2 • s4 • s3 • s4)}
  (trans (sym (move-product MV02125.proved (MV02126.proved))) (trans (cong refl Base.proved) (move-product MV02126.proved (MV02125.proved))))

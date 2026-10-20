{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02117 as MV02117
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02118 as MV02118
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0137 ≈ K0137 • M4
proved = GL.•-cancelʳ {g = M4 • K0137} {g' = K0137 • M4} {h = p (s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02117.proved (MV02118.proved))) (trans (cong refl Base.proved) (move-product MV02118.proved (MV02117.proved))))

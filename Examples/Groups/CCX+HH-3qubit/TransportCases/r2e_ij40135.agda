{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02113 as MV02113
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02114 as MV02114
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0135 ≈ K0135 • M4
proved = GL.•-cancelʳ {g = M4 • K0135} {g' = K0135 • M4} {h = p (s2 • s4 • s3 • s4)}
  (trans (sym (move-product MV02113.proved (MV02114.proved))) (trans (cong refl Base.proved) (move-product MV02114.proved (MV02113.proved))))

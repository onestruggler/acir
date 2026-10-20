{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02252 as MV02252
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02253 as MV02253
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K0135 ≈ K0135 • M6
proved = GL.•-cancelʳ {g = M6 • K0135} {g' = K0135 • M6} {h = p (s2 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02252.proved (MV02253.proved))) (trans (cong refl Base.proved) (move-product MV02253.proved (MV02252.proved))))

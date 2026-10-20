{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02260 as MV02260
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02261 as MV02261
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K0157 ≈ K0157 • M6
proved = GL.•-cancelʳ {g = M6 • K0157} {g' = K0157 • M6} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02260.proved (MV02261.proved))) (trans (cong refl Base.proved) (move-product MV02261.proved (MV02260.proved))))

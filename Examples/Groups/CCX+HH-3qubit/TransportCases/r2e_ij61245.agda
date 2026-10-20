{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij61245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1245 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02288 as MV02288
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02289 as MV02289
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K1245 ≈ K1245 • M6
proved = GL.•-cancelʳ {g = M6 • K1245} {g' = K1245 • M6} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02288.proved (MV02289.proved))) (trans (cong refl Base.proved) (move-product MV02289.proved (MV02288.proved))))

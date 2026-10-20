{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij61247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02290 as MV02290
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02291 as MV02291
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K1247 ≈ K1247 • M6
proved = GL.•-cancelʳ {g = M6 • K1247} {g' = K1247 • M6} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02290.proved (MV02291.proved))) (trans (cong refl Base.proved) (move-product MV02291.proved (MV02290.proved))))

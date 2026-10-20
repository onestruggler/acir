{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij31247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02081 as MV02081
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02082 as MV02082
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K1247 ≈ K1247 • M3
proved = GL.•-cancelʳ {g = M3 • K1247} {g' = K1247 • M3} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02081.proved (MV02082.proved))) (trans (cong refl Base.proved) (move-product MV02082.proved (MV02081.proved))))

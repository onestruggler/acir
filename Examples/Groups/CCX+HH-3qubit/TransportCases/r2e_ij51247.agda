{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij51247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02221 as MV02221
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02222 as MV02222
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K1247 ≈ K1247 • M5
proved = GL.•-cancelʳ {g = M5 • K1247} {g' = K1247 • M5} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02221.proved (MV02222.proved))) (trans (cong refl Base.proved) (move-product MV02222.proved (MV02221.proved))))

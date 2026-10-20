{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij51346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1346 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02225 as MV02225
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02226 as MV02226
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K1346 ≈ K1346 • M5
proved = GL.•-cancelʳ {g = M5 • K1346} {g' = K1346 • M5} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02225.proved (MV02226.proved))) (trans (cong refl Base.proved) (move-product MV02226.proved (MV02225.proved))))

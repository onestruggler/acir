{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij51267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1267 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02223 as MV02223
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02224 as MV02224
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K1267 ≈ K1267 • M5
proved = GL.•-cancelʳ {g = M5 • K1267} {g' = K1267 • M5} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02223.proved (MV02224.proved))) (trans (cong refl Base.proved) (move-product MV02224.proved (MV02223.proved))))

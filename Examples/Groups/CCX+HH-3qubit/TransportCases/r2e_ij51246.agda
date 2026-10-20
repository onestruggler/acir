{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij51246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02219 as MV02219
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02220 as MV02220
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K1246 ≈ K1246 • M5
proved = GL.•-cancelʳ {g = M5 • K1246} {g' = K1246 • M5} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02219.proved (MV02220.proved))) (trans (cong refl Base.proved) (move-product MV02220.proved (MV02219.proved))))

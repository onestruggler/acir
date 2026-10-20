{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij31246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02079 as MV02079
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02080 as MV02080
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K1246 ≈ K1246 • M3
proved = GL.•-cancelʳ {g = M3 • K1246} {g' = K1246 • M3} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02079.proved (MV02080.proved))) (trans (cong refl Base.proved) (move-product MV02080.proved (MV02079.proved))))

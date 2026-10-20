{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij31257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1257 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02085 as MV02085
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02086 as MV02086
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K1257 ≈ K1257 • M3
proved = GL.•-cancelʳ {g = M3 • K1257} {g' = K1257 • M3} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02085.proved (MV02086.proved))) (trans (cong refl Base.proved) (move-product MV02086.proved (MV02085.proved))))

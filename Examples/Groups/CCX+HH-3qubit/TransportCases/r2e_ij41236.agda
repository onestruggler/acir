{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij41236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1236 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02147 as MV02147
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02148 as MV02148
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K1236 ≈ K1236 • M4
proved = GL.•-cancelʳ {g = M4 • K1236} {g' = K1236 • M4} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02147.proved (MV02148.proved))) (trans (cong refl Base.proved) (move-product MV02148.proved (MV02147.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij51236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1236 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02215 as MV02215
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02216 as MV02216
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K1236 ≈ K1236 • M5
proved = GL.•-cancelʳ {g = M5 • K1236} {g' = K1236 • M5} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02215.proved (MV02216.proved))) (trans (cong refl Base.proved) (move-product MV02216.proved (MV02215.proved))))

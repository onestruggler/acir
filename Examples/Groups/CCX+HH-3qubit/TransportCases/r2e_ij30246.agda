{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02059 as MV02059
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02060 as MV02060
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0246 ≈ K0246 • M3
proved = GL.•-cancelʳ {g = M3 • K0246} {g' = K0246 • M3} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02059.proved (MV02060.proved))) (trans (cong refl Base.proved) (move-product MV02060.proved (MV02059.proved))))

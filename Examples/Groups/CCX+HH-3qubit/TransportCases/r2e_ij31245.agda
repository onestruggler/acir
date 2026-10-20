{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij31245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1245 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02077 as MV02077
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02078 as MV02078
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K1245 ≈ K1245 • M3
proved = GL.•-cancelʳ {g = M3 • K1245} {g' = K1245 • M3} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s4)}
  (trans (sym (move-product MV02077.proved (MV02078.proved))) (trans (cong refl Base.proved) (move-product MV02078.proved (MV02077.proved))))

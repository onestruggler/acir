{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij32567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2567 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02103 as MV02103
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02104 as MV02104
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K2567 ≈ K2567 • M3
proved = GL.•-cancelʳ {g = M3 • K2567} {g' = K2567 • M3} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02103.proved (MV02104.proved))) (trans (cong refl Base.proved) (move-product MV02104.proved (MV02103.proved))))

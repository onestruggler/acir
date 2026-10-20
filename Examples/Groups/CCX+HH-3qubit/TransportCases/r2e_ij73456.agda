{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij73456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3456 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02379 as MV02379
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02380 as MV02380
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K3456 ≈ K3456 • M7
proved = GL.•-cancelʳ {g = M7 • K3456} {g' = K3456 • M7} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02379.proved (MV02380.proved))) (trans (cong refl Base.proved) (move-product MV02380.proved (MV02379.proved))))

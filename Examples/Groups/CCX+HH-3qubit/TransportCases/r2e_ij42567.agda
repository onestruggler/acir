{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij42567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2567 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02171 as MV02171
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02172 as MV02172
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K2567 ≈ K2567 • M4
proved = GL.•-cancelʳ {g = M4 • K2567} {g' = K2567 • M4} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02171.proved (MV02172.proved))) (trans (cong refl Base.proved) (move-product MV02172.proved (MV02171.proved))))

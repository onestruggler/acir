{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij42367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2367 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02169 as MV02169
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02170 as MV02170
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K2367 ≈ K2367 • M4
proved = GL.•-cancelʳ {g = M4 • K2367} {g' = K2367 • M4} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02169.proved (MV02170.proved))) (trans (cong refl Base.proved) (move-product MV02170.proved (MV02169.proved))))

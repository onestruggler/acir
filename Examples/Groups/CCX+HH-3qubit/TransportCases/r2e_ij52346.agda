{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij52346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2346 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02233 as MV02233
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02234 as MV02234
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K2346 ≈ K2346 • M5
proved = GL.•-cancelʳ {g = M5 • K2346} {g' = K2346 • M5} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02233.proved (MV02234.proved))) (trans (cong refl Base.proved) (move-product MV02234.proved (MV02233.proved))))

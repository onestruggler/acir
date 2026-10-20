{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0247 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02201 as MV02201
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02202 as MV02202
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0247 ≈ K0247 • M5
proved = GL.•-cancelʳ {g = M5 • K0247} {g' = K0247 • M5} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02201.proved (MV02202.proved))) (trans (cong refl Base.proved) (move-product MV02202.proved (MV02201.proved))))

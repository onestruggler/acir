{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0247 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02270 as MV02270
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02271 as MV02271
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K0247 ≈ K0247 • M6
proved = GL.•-cancelʳ {g = M6 • K0247} {g' = K0247 • M6} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02270.proved (MV02271.proved))) (trans (cong refl Base.proved) (move-product MV02271.proved (MV02270.proved))))

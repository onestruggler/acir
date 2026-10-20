{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij24567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02040 as MV02040
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02041 as MV02041
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K4567 ≈ K4567 • M2
proved = GL.•-cancelʳ {g = M2 • K4567} {g' = K4567 • M2} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02040.proved (MV02041.proved))) (trans (cong refl Base.proved) (move-product MV02041.proved (MV02040.proved))))

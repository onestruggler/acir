{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1456 ; M4 ; M6 ; X14 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00691 as MV00691
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02755 as MV02755
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02756 as MV02756
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02757 as MV02757
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02758 as MV02758
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X14 • K1456 ≈ K1456 • X46 • M4 • M6
proved = GL.•-cancelʳ {g = X14 • K1456} {g' = K1456 • X46 • M4 • M6} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02755.proved (MV00691.proved))) (trans (cong refl Base.proved) (move-product MV00691.proved (move-product MV02756.proved (move-product MV02757.proved (MV02758.proved))))))

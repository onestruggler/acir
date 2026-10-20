{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1456 ; M1 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00691 as MV00691
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02926 as MV02926
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02927 as MV02927
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X45 • K1456 ≈ M1 • K1456 • M1 • K1456 • M1
proved = GL.•-cancelʳ {g = X45 • K1456} {g' = M1 • K1456 • M1 • K1456 • M1} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02926.proved (MV00691.proved))) (trans (cong refl Base.proved) (move-product MV02927.proved (move-product MV00691.proved (move-product MV02927.proved (move-product MV00691.proved (MV02927.proved)))))))

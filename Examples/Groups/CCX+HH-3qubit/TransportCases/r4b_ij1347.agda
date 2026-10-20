{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1347 ; M1 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00687 as MV00687
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02918 as MV02918
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02919 as MV02919
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X34 • K1347 ≈ M1 • K1347 • M1 • K1347 • M1
proved = GL.•-cancelʳ {g = X34 • K1347} {g' = M1 • K1347 • M1 • K1347 • M1} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02918.proved (MV00687.proved))) (trans (cong refl Base.proved) (move-product MV02919.proved (move-product MV00687.proved (move-product MV02919.proved (move-product MV00687.proved (MV02919.proved)))))))

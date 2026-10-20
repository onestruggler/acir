{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; M1 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00681 as MV00681
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02906 as MV02906
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02907 as MV02907
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X24 • K1247 ≈ M1 • K1247 • M1 • K1247 • M1
proved = GL.•-cancelʳ {g = X24 • K1247} {g' = M1 • K1247 • M1 • K1247 • M1} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02906.proved (MV00681.proved))) (trans (cong refl Base.proved) (move-product MV02907.proved (move-product MV00681.proved (move-product MV02907.proved (move-product MV00681.proved (MV02907.proved)))))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; M0 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00653 as MV00653
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02852 as MV02852
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02853 as MV02853
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X15 • K0157 ≈ M0 • K0157 • M0 • K0157 • M0
proved = GL.•-cancelʳ {g = X15 • K0157} {g' = M0 • K0157 • M0 • K0157 • M0} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02852.proved (MV00653.proved))) (trans (cong refl Base.proved) (move-product MV02853.proved (move-product MV00653.proved (move-product MV02853.proved (move-product MV00653.proved (MV02853.proved)))))))

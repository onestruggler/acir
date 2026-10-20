{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; M0 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00659 as MV00659
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02863 as MV02863
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02864 as MV02864
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X24 • K0245 ≈ M0 • K0245 • M0 • K0245 • M0
proved = GL.•-cancelʳ {g = X24 • K0245} {g' = M0 • K0245 • M0 • K0245 • M0} {h = p (s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02863.proved (MV00659.proved))) (trans (cong refl Base.proved) (move-product MV02864.proved (move-product MV00659.proved (move-product MV02864.proved (move-product MV00659.proved (MV02864.proved)))))))

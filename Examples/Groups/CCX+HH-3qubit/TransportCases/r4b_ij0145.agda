{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; M0 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00649 as MV00649
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02844 as MV02844
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02845 as MV02845
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X14 • K0145 ≈ M0 • K0145 • M0 • K0145 • M0
proved = GL.•-cancelʳ {g = X14 • K0145} {g' = M0 • K0145 • M0 • K0145 • M0} {h = p (s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02844.proved (MV00649.proved))) (trans (cong refl Base.proved) (move-product MV02845.proved (move-product MV00649.proved (move-product MV02845.proved (move-product MV00649.proved (MV02845.proved)))))))

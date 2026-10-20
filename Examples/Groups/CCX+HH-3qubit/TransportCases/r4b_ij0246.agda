{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; M0 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00660 as MV00660
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02865 as MV02865
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02866 as MV02866
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X24 • K0246 ≈ M0 • K0246 • M0 • K0246 • M0
proved = GL.•-cancelʳ {g = X24 • K0246} {g' = M0 • K0246 • M0 • K0246 • M0} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02865.proved (MV00660.proved))) (trans (cong refl Base.proved) (move-product MV02866.proved (move-product MV00660.proved (move-product MV02866.proved (move-product MV00660.proved (MV02866.proved)))))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; M0 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00650 as MV00650
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02846 as MV02846
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02847 as MV02847
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X14 • K0146 ≈ M0 • K0146 • M0 • K0146 • M0
proved = GL.•-cancelʳ {g = X14 • K0146} {g' = M0 • K0146 • M0 • K0146 • M0} {h = p (s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02846.proved (MV00650.proved))) (trans (cong refl Base.proved) (move-product MV02847.proved (move-product MV00650.proved (move-product MV02847.proved (move-product MV00650.proved (MV02847.proved)))))))

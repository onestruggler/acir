{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; M0 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00642 as MV00642
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02831 as MV02831
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02832 as MV02832
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X12 • K0125 ≈ M0 • K0125 • M0 • K0125 • M0
proved = GL.•-cancelʳ {g = X12 • K0125} {g' = M0 • K0125 • M0 • K0125 • M0} {h = p (s4 • s3)}
  (trans (sym (move-product MV02831.proved (MV00642.proved))) (trans (cong refl Base.proved) (move-product MV02832.proved (move-product MV00642.proved (move-product MV02832.proved (move-product MV00642.proved (MV02832.proved)))))))

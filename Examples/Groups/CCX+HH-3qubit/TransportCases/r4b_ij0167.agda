{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; M0 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00654 as MV00654
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02854 as MV02854
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02855 as MV02855
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X16 • K0167 ≈ M0 • K0167 • M0 • K0167 • M0
proved = GL.•-cancelʳ {g = X16 • K0167} {g' = M0 • K0167 • M0 • K0167 • M0} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02854.proved (MV00654.proved))) (trans (cong refl Base.proved) (move-product MV02855.proved (move-product MV00654.proved (move-product MV02855.proved (move-product MV00654.proved (MV02855.proved)))))))

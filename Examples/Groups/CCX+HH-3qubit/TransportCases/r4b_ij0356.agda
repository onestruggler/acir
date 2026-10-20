{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; M0 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00668 as MV00668
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02881 as MV02881
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02882 as MV02882
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X35 • K0356 ≈ M0 • K0356 • M0 • K0356 • M0
proved = GL.•-cancelʳ {g = X35 • K0356} {g' = M0 • K0356 • M0 • K0356 • M0} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02881.proved (MV00668.proved))) (trans (cong refl Base.proved) (move-product MV02882.proved (move-product MV00668.proved (move-product MV02882.proved (move-product MV00668.proved (MV02882.proved)))))))

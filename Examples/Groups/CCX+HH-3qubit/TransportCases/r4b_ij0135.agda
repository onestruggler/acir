{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; M0 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00646 as MV00646
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02838 as MV02838
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02839 as MV02839
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X13 • K0135 ≈ M0 • K0135 • M0 • K0135 • M0
proved = GL.•-cancelʳ {g = X13 • K0135} {g' = M0 • K0135 • M0 • K0135 • M0} {h = p (s2 • s4 • s3)}
  (trans (sym (move-product MV02838.proved (MV00646.proved))) (trans (cong refl Base.proved) (move-product MV02839.proved (move-product MV00646.proved (move-product MV02839.proved (move-product MV00646.proved (MV02839.proved)))))))

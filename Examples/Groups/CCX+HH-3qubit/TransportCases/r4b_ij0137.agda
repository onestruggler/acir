{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; M0 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00648 as MV00648
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02842 as MV02842
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02843 as MV02843
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X13 • K0137 ≈ M0 • K0137 • M0 • K0137 • M0
proved = GL.•-cancelʳ {g = X13 • K0137} {g' = M0 • K0137 • M0 • K0137 • M0} {h = p (s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02842.proved (MV00648.proved))) (trans (cong refl Base.proved) (move-product MV02843.proved (move-product MV00648.proved (move-product MV02843.proved (move-product MV00648.proved (MV02843.proved)))))))

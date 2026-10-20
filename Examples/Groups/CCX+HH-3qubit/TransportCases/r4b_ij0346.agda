{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; M0 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00666 as MV00666
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02877 as MV02877
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02878 as MV02878
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X34 • K0346 ≈ M0 • K0346 • M0 • K0346 • M0
proved = GL.•-cancelʳ {g = X34 • K0346} {g' = M0 • K0346 • M0 • K0346 • M0} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02877.proved (MV00666.proved))) (trans (cong refl Base.proved) (move-product MV02878.proved (move-product MV00666.proved (move-product MV02878.proved (move-product MV00666.proved (MV02878.proved)))))))

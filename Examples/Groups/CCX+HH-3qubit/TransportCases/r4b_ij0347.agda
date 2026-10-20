{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; M0 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00667 as MV00667
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02879 as MV02879
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02880 as MV02880
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X34 • K0347 ≈ M0 • K0347 • M0 • K0347 • M0
proved = GL.•-cancelʳ {g = X34 • K0347} {g' = M0 • K0347 • M0 • K0347 • M0} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02879.proved (MV00667.proved))) (trans (cong refl Base.proved) (move-product MV02880.proved (move-product MV00667.proved (move-product MV02880.proved (move-product MV00667.proved (MV02880.proved)))))))

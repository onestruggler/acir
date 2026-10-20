{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; M0 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00656 as MV00656
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02857 as MV02857
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02858 as MV02858
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X23 • K0235 ≈ M0 • K0235 • M0 • K0235 • M0
proved = GL.•-cancelʳ {g = X23 • K0235} {g' = M0 • K0235 • M0 • K0235 • M0} {h = p (s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV02857.proved (MV00656.proved))) (trans (cong refl Base.proved) (move-product MV02858.proved (move-product MV00656.proved (move-product MV02858.proved (move-product MV00656.proved (MV02858.proved)))))))

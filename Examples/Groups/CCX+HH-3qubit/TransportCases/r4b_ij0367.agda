{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; M0 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00670 as MV00670
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02885 as MV02885
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02886 as MV02886
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X36 • K0367 ≈ M0 • K0367 • M0 • K0367 • M0
proved = GL.•-cancelʳ {g = X36 • K0367} {g' = M0 • K0367 • M0 • K0367 • M0} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02885.proved (MV00670.proved))) (trans (cong refl Base.proved) (move-product MV02886.proved (move-product MV00670.proved (move-product MV02886.proved (move-product MV00670.proved (MV02886.proved)))))))

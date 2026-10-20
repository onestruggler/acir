{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; M0 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00658 as MV00658
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02861 as MV02861
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02862 as MV02862
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X23 • K0237 ≈ M0 • K0237 • M0 • K0237 • M0
proved = GL.•-cancelʳ {g = X23 • K0237} {g' = M0 • K0237 • M0 • K0237 • M0} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02861.proved (MV00658.proved))) (trans (cong refl Base.proved) (move-product MV02862.proved (move-product MV00658.proved (move-product MV02862.proved (move-product MV00658.proved (MV02862.proved)))))))

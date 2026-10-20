{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0357 ; M0 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00669 as MV00669
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02883 as MV02883
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02884 as MV02884
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X35 • K0357 ≈ M0 • K0357 • M0 • K0357 • M0
proved = GL.•-cancelʳ {g = X35 • K0357} {g' = M0 • K0357 • M0 • K0357 • M0} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02883.proved (MV00669.proved))) (trans (cong refl Base.proved) (move-product MV02884.proved (move-product MV00669.proved (move-product MV02884.proved (move-product MV00669.proved (MV02884.proved)))))))

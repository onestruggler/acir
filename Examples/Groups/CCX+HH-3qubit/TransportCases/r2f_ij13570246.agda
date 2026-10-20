{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij13570246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; K1357 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00689 as MV00689
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02429 as MV02429
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1357 • K0246 ≈ K0246 • K1357
proved = GL.•-cancelʳ {g = K1357 • K0246} {g' = K0246 • K1357} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00689.proved (MV02429.proved))) (trans (cong refl Base.proved) (move-product MV02429.proved (MV00689.proved))))

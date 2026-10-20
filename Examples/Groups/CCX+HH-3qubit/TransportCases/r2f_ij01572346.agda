{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01572346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; K2346 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00653 as MV00653
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02393 as MV02393
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0157 • K2346 ≈ K2346 • K0157
proved = GL.•-cancelʳ {g = K0157 • K2346} {g' = K2346 • K0157} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00653.proved (MV02393.proved))) (trans (cong refl Base.proved) (move-product MV02393.proved (MV00653.proved))))

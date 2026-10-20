{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01462357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; K2357 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00650 as MV00650
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02390 as MV02390
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0146 • K2357 ≈ K2357 • K0146
proved = GL.•-cancelʳ {g = K0146 • K2357} {g' = K2357 • K0146} {h = p (s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00650.proved (MV02390.proved))) (trans (cong refl Base.proved) (move-product MV02390.proved (MV00650.proved))))

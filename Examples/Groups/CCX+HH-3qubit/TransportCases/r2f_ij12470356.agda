{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12470356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; K1247 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00681 as MV00681
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02421 as MV02421
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1247 • K0356 ≈ K0356 • K1247
proved = GL.•-cancelʳ {g = K1247 • K0356} {g' = K0356 • K1247} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00681.proved (MV02421.proved))) (trans (cong refl Base.proved) (move-product MV02421.proved (MV00681.proved))))

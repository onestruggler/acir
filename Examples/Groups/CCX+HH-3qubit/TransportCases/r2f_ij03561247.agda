{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij03561247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; K1247 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00668 as MV00668
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02408 as MV02408
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0356 • K1247 ≈ K1247 • K0356
proved = GL.•-cancelʳ {g = K0356 • K1247} {g' = K1247 • K0356} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00668.proved (MV02408.proved))) (trans (cong refl Base.proved) (move-product MV02408.proved (MV00668.proved))))

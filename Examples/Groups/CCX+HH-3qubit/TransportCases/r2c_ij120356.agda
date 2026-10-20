{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij120356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00668 as MV00668
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01212 as MV01212
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X12 • K0356 ≈ K0356 • X12
proved = GL.•-cancelʳ {g = X12 • K0356} {g' = K0356 • X12} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01212.proved (MV00668.proved))) (trans (cong refl Base.proved) (move-product MV00668.proved (MV01212.proved))))

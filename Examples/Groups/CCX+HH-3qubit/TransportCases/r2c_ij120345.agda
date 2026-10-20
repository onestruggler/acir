{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij120345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00665 as MV00665
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01209 as MV01209
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X12 • K0345 ≈ K0345 • X12
proved = GL.•-cancelʳ {g = X12 • K0345} {g' = K0345 • X12} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01209.proved (MV00665.proved))) (trans (cong refl Base.proved) (move-product MV00665.proved (MV01209.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01321 as MV01321
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01322 as MV01322
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K0345 ≈ K0345 • X16
proved = GL.•-cancelʳ {g = X16 • K0345} {g' = K0345 • X16} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01321.proved (MV01322.proved))) (trans (cong refl Base.proved) (move-product MV01322.proved (MV01321.proved))))

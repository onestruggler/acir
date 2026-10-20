{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01327 as MV01327
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01328 as MV01328
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K0457 ≈ K0457 • X16
proved = GL.•-cancelʳ {g = X16 • K0457} {g' = K0457 • X16} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01327.proved (MV01328.proved))) (trans (cong refl Base.proved) (move-product MV01328.proved (MV01327.proved))))

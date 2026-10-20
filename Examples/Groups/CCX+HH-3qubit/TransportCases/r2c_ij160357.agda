{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0357 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01325 as MV01325
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01326 as MV01326
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K0357 ≈ K0357 • X16
proved = GL.•-cancelʳ {g = X16 • K0357} {g' = K0357 • X16} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01325.proved (MV01326.proved))) (trans (cong refl Base.proved) (move-product MV01326.proved (MV01325.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; X16 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00650 as MV00650
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02592 as MV02592
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02972 as MV02972
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X46 • K0146 ≈ K0146 • X16
proved = GL.•-cancelʳ {g = X46 • K0146} {g' = K0146 • X16} {h = p (s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02972.proved (MV00650.proved))) (trans (cong refl Base.proved) (move-product MV00650.proved (MV02592.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; X16 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00652 as MV00652
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02600 as MV02600
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02974 as MV02974
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X56 • K0156 ≈ K0156 • X16
proved = GL.•-cancelʳ {g = X56 • K0156} {g' = K0156 • X16} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02974.proved (MV00652.proved))) (trans (cong refl Base.proved) (move-product MV00652.proved (MV02600.proved))))

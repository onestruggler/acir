{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; X16 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00647 as MV00647
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02580 as MV02580
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02969 as MV02969
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X36 • K0136 ≈ K0136 • X16
proved = GL.•-cancelʳ {g = X36 • K0136} {g' = K0136 • X16} {h = p (s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02969.proved (MV00647.proved))) (trans (cong refl Base.proved) (move-product MV00647.proved (MV02580.proved))))

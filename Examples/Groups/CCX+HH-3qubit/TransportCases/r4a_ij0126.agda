{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; M1 ; M6 ; X01 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00643 as MV00643
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02563 as MV02563
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02564 as MV02564
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02565 as MV02565
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02566 as MV02566
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X01 • K0126 ≈ K0126 • X16 • M1 • M6
proved = GL.•-cancelʳ {g = X01 • K0126} {g' = K0126 • X16 • M1 • M6} {h = p (s5 • s4 • s3)}
  (trans (sym (move-product MV02563.proved (MV00643.proved))) (trans (cong refl Base.proved) (move-product MV00643.proved (move-product MV02564.proved (move-product MV02565.proved (MV02566.proved))))))

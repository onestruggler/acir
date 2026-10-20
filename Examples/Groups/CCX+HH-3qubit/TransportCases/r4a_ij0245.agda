{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; M2 ; M5 ; X02 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00659 as MV00659
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02627 as MV02627
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02628 as MV02628
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02629 as MV02629
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02630 as MV02630
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X02 • K0245 ≈ K0245 • X25 • M2 • M5
proved = GL.•-cancelʳ {g = X02 • K0245} {g' = K0245 • X25 • M2 • M5} {h = p (s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02627.proved (MV00659.proved))) (trans (cong refl Base.proved) (move-product MV00659.proved (move-product MV02628.proved (move-product MV02629.proved (MV02630.proved))))))

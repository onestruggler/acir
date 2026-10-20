{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; M1 ; M5 ; X01 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00642 as MV00642
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02559 as MV02559
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02560 as MV02560
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02561 as MV02561
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02562 as MV02562
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X01 • K0125 ≈ K0125 • X15 • M1 • M5
proved = GL.•-cancelʳ {g = X01 • K0125} {g' = K0125 • X15 • M1 • M5} {h = p (s4 • s3)}
  (trans (sym (move-product MV02559.proved (MV00642.proved))) (trans (cong refl Base.proved) (move-product MV00642.proved (move-product MV02560.proved (move-product MV02561.proved (MV02562.proved))))))

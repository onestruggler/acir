{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; M1 ; M6 ; X01 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00647 as MV00647
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02579 as MV02579
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02580 as MV02580
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02581 as MV02581
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02582 as MV02582
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X01 • K0136 ≈ K0136 • X16 • M1 • M6
proved = GL.•-cancelʳ {g = X01 • K0136} {g' = K0136 • X16 • M1 • M6} {h = p (s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02579.proved (MV00647.proved))) (trans (cong refl Base.proved) (move-product MV00647.proved (move-product MV02580.proved (move-product MV02581.proved (MV02582.proved))))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; M1 ; M6 ; X01 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00650 as MV00650
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02591 as MV02591
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02592 as MV02592
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02593 as MV02593
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02594 as MV02594
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X01 • K0146 ≈ K0146 • X16 • M1 • M6
proved = GL.•-cancelʳ {g = X01 • K0146} {g' = K0146 • X16 • M1 • M6} {h = p (s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02591.proved (MV00650.proved))) (trans (cong refl Base.proved) (move-product MV00650.proved (move-product MV02592.proved (move-product MV02593.proved (MV02594.proved))))))

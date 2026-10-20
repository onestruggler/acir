{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; M1 ; M7 ; X01 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00653 as MV00653
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02603 as MV02603
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02604 as MV02604
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02605 as MV02605
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02606 as MV02606
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X01 • K0157 ≈ K0157 • X17 • M1 • M7
proved = GL.•-cancelʳ {g = X01 • K0157} {g' = K0157 • X17 • M1 • M7} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02603.proved (MV00653.proved))) (trans (cong refl Base.proved) (move-product MV00653.proved (move-product MV02604.proved (move-product MV02605.proved (MV02606.proved))))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; M1 ; M7 ; X01 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00654 as MV00654
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02607 as MV02607
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02608 as MV02608
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02609 as MV02609
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02610 as MV02610
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X01 • K0167 ≈ K0167 • X17 • M1 • M7
proved = GL.•-cancelʳ {g = X01 • K0167} {g' = K0167 • X17 • M1 • M7} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02607.proved (MV00654.proved))) (trans (cong refl Base.proved) (move-product MV00654.proved (move-product MV02608.proved (move-product MV02609.proved (MV02610.proved))))))

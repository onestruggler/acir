{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; M1 ; M7 ; X01 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00644 as MV00644
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02567 as MV02567
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02568 as MV02568
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02569 as MV02569
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02570 as MV02570
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X01 • K0127 ≈ K0127 • X17 • M1 • M7
proved = GL.•-cancelʳ {g = X01 • K0127} {g' = K0127 • X17 • M1 • M7} {h = p (s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02567.proved (MV00644.proved))) (trans (cong refl Base.proved) (move-product MV00644.proved (move-product MV02568.proved (move-product MV02569.proved (MV02570.proved))))))

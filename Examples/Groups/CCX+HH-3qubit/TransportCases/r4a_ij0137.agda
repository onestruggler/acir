{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; M1 ; M7 ; X01 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00648 as MV00648
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02583 as MV02583
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02584 as MV02584
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02585 as MV02585
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02586 as MV02586
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X01 • K0137 ≈ K0137 • X17 • M1 • M7
proved = GL.•-cancelʳ {g = X01 • K0137} {g' = K0137 • X17 • M1 • M7} {h = p (s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02583.proved (MV00648.proved))) (trans (cong refl Base.proved) (move-product MV00648.proved (move-product MV02584.proved (move-product MV02585.proved (MV02586.proved))))))

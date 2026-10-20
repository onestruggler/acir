{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; M5 ; M7 ; X05 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00674 as MV00674
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02687 as MV02687
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02688 as MV02688
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02689 as MV02689
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02690 as MV02690
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X05 • K0567 ≈ K0567 • X57 • M5 • M7
proved = GL.•-cancelʳ {g = X05 • K0567} {g' = K0567 • X57 • M5 • M7} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02687.proved (MV00674.proved))) (trans (cong refl Base.proved) (move-product MV00674.proved (move-product MV02688.proved (move-product MV02689.proved (MV02690.proved))))))

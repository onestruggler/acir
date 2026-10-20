{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; M0 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00674 as MV00674
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02893 as MV02893
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02894 as MV02894
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X56 • K0567 ≈ M0 • K0567 • M0 • K0567 • M0
proved = GL.•-cancelʳ {g = X56 • K0567} {g' = M0 • K0567 • M0 • K0567 • M0} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02893.proved (MV00674.proved))) (trans (cong refl Base.proved) (move-product MV02894.proved (move-product MV00674.proved (move-product MV02894.proved (move-product MV00674.proved (MV02894.proved)))))))

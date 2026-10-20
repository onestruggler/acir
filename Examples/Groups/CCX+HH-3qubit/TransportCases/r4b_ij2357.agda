{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2357 ; M2 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00699 as MV00699
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02942 as MV02942
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02943 as MV02943
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X35 • K2357 ≈ M2 • K2357 • M2 • K2357 • M2
proved = GL.•-cancelʳ {g = X35 • K2357} {g' = M2 • K2357 • M2 • K2357 • M2} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02942.proved (MV00699.proved))) (trans (cong refl Base.proved) (move-product MV02943.proved (move-product MV00699.proved (move-product MV02943.proved (move-product MV00699.proved (MV02943.proved)))))))

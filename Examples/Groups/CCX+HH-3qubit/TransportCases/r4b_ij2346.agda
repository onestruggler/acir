{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2346 ; M2 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00696 as MV00696
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02936 as MV02936
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02937 as MV02937
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X34 • K2346 ≈ M2 • K2346 • M2 • K2346 • M2
proved = GL.•-cancelʳ {g = X34 • K2346} {g' = M2 • K2346 • M2 • K2346 • M2} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02936.proved (MV00696.proved))) (trans (cong refl Base.proved) (move-product MV02937.proved (move-product MV00696.proved (move-product MV02937.proved (move-product MV00696.proved (MV02937.proved)))))))

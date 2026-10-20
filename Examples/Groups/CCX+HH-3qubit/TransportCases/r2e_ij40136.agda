{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02115 as MV02115
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02116 as MV02116
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0136 ≈ K0136 • M4
proved = GL.•-cancelʳ {g = M4 • K0136} {g' = K0136 • M4} {h = p (s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02115.proved (MV02116.proved))) (trans (cong refl Base.proved) (move-product MV02116.proved (MV02115.proved))))

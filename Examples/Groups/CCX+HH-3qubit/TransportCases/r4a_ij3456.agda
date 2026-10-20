{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij3456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3456 ; M4 ; M6 ; X34 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00705 as MV00705
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02811 as MV02811
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02812 as MV02812
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02813 as MV02813
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02814 as MV02814
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X34 • K3456 ≈ K3456 • X46 • M4 • M6
proved = GL.•-cancelʳ {g = X34 • K3456} {g' = K3456 • X46 • M4 • M6} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02811.proved (MV00705.proved))) (trans (cong refl Base.proved) (move-product MV00705.proved (move-product MV02812.proved (move-product MV02813.proved (MV02814.proved))))))

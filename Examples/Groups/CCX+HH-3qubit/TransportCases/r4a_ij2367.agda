{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2367 ; M3 ; M7 ; X23 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00700 as MV00700
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02791 as MV02791
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02792 as MV02792
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02793 as MV02793
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02794 as MV02794
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X23 • K2367 ≈ K2367 • X37 • M3 • M7
proved = GL.•-cancelʳ {g = X23 • K2367} {g' = K2367 • X37 • M3 • M7} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02791.proved (MV00700.proved))) (trans (cong refl Base.proved) (move-product MV00700.proved (move-product MV02792.proved (move-product MV02793.proved (MV02794.proved))))))

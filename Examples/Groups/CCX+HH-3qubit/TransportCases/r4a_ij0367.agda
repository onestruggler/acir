{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; M3 ; M7 ; X03 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00670 as MV00670
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02671 as MV02671
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02672 as MV02672
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02673 as MV02673
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02674 as MV02674
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X03 • K0367 ≈ K0367 • X37 • M3 • M7
proved = GL.•-cancelʳ {g = X03 • K0367} {g' = K0367 • X37 • M3 • M7} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02671.proved (MV00670.proved))) (trans (cong refl Base.proved) (move-product MV00670.proved (move-product MV02672.proved (move-product MV02673.proved (MV02674.proved))))))

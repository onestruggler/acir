{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; M4 ; M7 ; X24 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00703 as MV00703
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02803 as MV02803
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02804 as MV02804
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02805 as MV02805
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02806 as MV02806
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X24 • K2467 ≈ K2467 • X47 • M4 • M7
proved = GL.•-cancelʳ {g = X24 • K2467} {g' = K2467 • X47 • M4 • M7} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02803.proved (MV00703.proved))) (trans (cong refl Base.proved) (move-product MV00703.proved (move-product MV02804.proved (move-product MV02805.proved (MV02806.proved))))))

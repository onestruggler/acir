{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1257 ; M2 ; M7 ; X12 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00683 as MV00683
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02723 as MV02723
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02724 as MV02724
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02725 as MV02725
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02726 as MV02726
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X12 • K1257 ≈ K1257 • X27 • M2 • M7
proved = GL.•-cancelʳ {g = X12 • K1257} {g' = K1257 • X27 • M2 • M7} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02723.proved (MV00683.proved))) (trans (cong refl Base.proved) (move-product MV00683.proved (move-product MV02724.proved (move-product MV02725.proved (MV02726.proved))))))

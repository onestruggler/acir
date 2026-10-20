{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; M2 ; M7 ; X02 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00658 as MV00658
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02623 as MV02623
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02624 as MV02624
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02625 as MV02625
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02626 as MV02626
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X02 • K0237 ≈ K0237 • X27 • M2 • M7
proved = GL.•-cancelʳ {g = X02 • K0237} {g' = K0237 • X27 • M2 • M7} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02623.proved (MV00658.proved))) (trans (cong refl Base.proved) (move-product MV00658.proved (move-product MV02624.proved (move-product MV02625.proved (MV02626.proved))))))

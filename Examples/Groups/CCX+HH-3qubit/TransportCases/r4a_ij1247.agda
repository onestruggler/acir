{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; M2 ; M7 ; X12 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00681 as MV00681
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02715 as MV02715
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02716 as MV02716
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02717 as MV02717
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02718 as MV02718
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X12 • K1247 ≈ K1247 • X27 • M2 • M7
proved = GL.•-cancelʳ {g = X12 • K1247} {g' = K1247 • X27 • M2 • M7} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02715.proved (MV00681.proved))) (trans (cong refl Base.proved) (move-product MV00681.proved (move-product MV02716.proved (move-product MV02717.proved (MV02718.proved))))))

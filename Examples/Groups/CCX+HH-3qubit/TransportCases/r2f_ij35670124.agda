{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij35670124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K3567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00708 as MV00708
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02448 as MV02448
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K3567 • K0124 ≈ K0124 • K3567
proved = GL.•-cancelʳ {g = K3567 • K0124} {g' = K0124 • K3567} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00708.proved (MV02448.proved))) (trans (cong refl Base.proved) (move-product MV02448.proved (MV00708.proved))))

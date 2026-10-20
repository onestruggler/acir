{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij43567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3567 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02173 as MV02173
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02174 as MV02174
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K3567 ≈ K3567 • M4
proved = GL.•-cancelʳ {g = M4 • K3567} {g' = K3567 • M4} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02173.proved (MV02174.proved))) (trans (cong refl Base.proved) (move-product MV02174.proved (MV02173.proved))))

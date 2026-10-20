{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij23567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3567 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02038 as MV02038
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02039 as MV02039
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K3567 ≈ K3567 • M2
proved = GL.•-cancelʳ {g = M2 • K3567} {g' = K3567 • M2} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02038.proved (MV02039.proved))) (trans (cong refl Base.proved) (move-product MV02039.proved (MV02038.proved))))

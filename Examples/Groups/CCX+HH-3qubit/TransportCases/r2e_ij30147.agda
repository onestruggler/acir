{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02049 as MV02049
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02050 as MV02050
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0147 ≈ K0147 • M3
proved = GL.•-cancelʳ {g = M3 • K0147} {g' = K0147 • M3} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02049.proved (MV02050.proved))) (trans (cong refl Base.proved) (move-product MV02050.proved (MV02049.proved))))

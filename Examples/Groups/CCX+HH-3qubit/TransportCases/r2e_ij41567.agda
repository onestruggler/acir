{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij41567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1567 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02163 as MV02163
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02164 as MV02164
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K1567 ≈ K1567 • M4
proved = GL.•-cancelʳ {g = M4 • K1567} {g' = K1567 • M4} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02163.proved (MV02164.proved))) (trans (cong refl Base.proved) (move-product MV02164.proved (MV02163.proved))))

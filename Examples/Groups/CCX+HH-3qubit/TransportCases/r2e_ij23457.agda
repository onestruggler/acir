{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij23457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3457 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02034 as MV02034
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02035 as MV02035
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K3457 ≈ K3457 • M2
proved = GL.•-cancelʳ {g = M2 • K3457} {g' = K3457 • M2} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02034.proved (MV02035.proved))) (trans (cong refl Base.proved) (move-product MV02035.proved (MV02034.proved))))

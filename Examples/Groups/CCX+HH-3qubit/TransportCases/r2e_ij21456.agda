{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij21456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1456 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02024 as MV02024
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02025 as MV02025
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K1456 ≈ K1456 • M2
proved = GL.•-cancelʳ {g = M2 • K1456} {g' = K1456 • M2} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02024.proved (MV02025.proved))) (trans (cong refl Base.proved) (move-product MV02025.proved (MV02024.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij21356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1356 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02018 as MV02018
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02019 as MV02019
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K1356 ≈ K1356 • M2
proved = GL.•-cancelʳ {g = M2 • K1356} {g' = K1356 • M2} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02018.proved (MV02019.proved))) (trans (cong refl Base.proved) (move-product MV02019.proved (MV02018.proved))))

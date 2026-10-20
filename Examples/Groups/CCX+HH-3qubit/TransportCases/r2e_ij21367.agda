{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij21367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1367 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02022 as MV02022
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02023 as MV02023
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K1367 ≈ K1367 • M2
proved = GL.•-cancelʳ {g = M2 • K1367} {g' = K1367 • M2} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02022.proved (MV02023.proved))) (trans (cong refl Base.proved) (move-product MV02023.proved (MV02022.proved))))

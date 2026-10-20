{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij71346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1346 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02365 as MV02365
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02366 as MV02366
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K1346 ≈ K1346 • M7
proved = GL.•-cancelʳ {g = M7 • K1346} {g' = K1346 • M7} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02365.proved (MV02366.proved))) (trans (cong refl Base.proved) (move-product MV02366.proved (MV02365.proved))))

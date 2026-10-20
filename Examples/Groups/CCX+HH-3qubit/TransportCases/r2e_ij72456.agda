{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij72456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2456 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02377 as MV02377
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02378 as MV02378
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K2456 ≈ K2456 • M7
proved = GL.•-cancelʳ {g = M7 • K2456} {g' = K2456 • M7} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02377.proved (MV02378.proved))) (trans (cong refl Base.proved) (move-product MV02378.proved (MV02377.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02343 as MV02343
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02344 as MV02344
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K0345 ≈ K0345 • M7
proved = GL.•-cancelʳ {g = M7 • K0345} {g' = K0345 • M7} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02343.proved (MV02344.proved))) (trans (cong refl Base.proved) (move-product MV02344.proved (MV02343.proved))))

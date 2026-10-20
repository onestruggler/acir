{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02345 as MV02345
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02346 as MV02346
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K0346 ≈ K0346 • M7
proved = GL.•-cancelʳ {g = M7 • K0346} {g' = K0346 • M7} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02345.proved (MV02346.proved))) (trans (cong refl Base.proved) (move-product MV02346.proved (MV02345.proved))))

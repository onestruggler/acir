{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1467 ; M1 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00693 as MV00693
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02930 as MV02930
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02931 as MV02931
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X46 • K1467 ≈ M1 • K1467 • M1 • K1467 • M1
proved = GL.•-cancelʳ {g = X46 • K1467} {g' = M1 • K1467 • M1 • K1467 • M1} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02930.proved (MV00693.proved))) (trans (cong refl Base.proved) (move-product MV02931.proved (move-product MV00693.proved (move-product MV02931.proved (move-product MV00693.proved (MV02931.proved)))))))

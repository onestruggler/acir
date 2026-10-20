{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2347 ; M2 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00697 as MV00697
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02938 as MV02938
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02939 as MV02939
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X34 • K2347 ≈ M2 • K2347 • M2 • K2347 • M2
proved = GL.•-cancelʳ {g = X34 • K2347} {g' = M2 • K2347 • M2 • K2347 • M2} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02938.proved (MV00697.proved))) (trans (cong refl Base.proved) (move-product MV02939.proved (move-product MV00697.proved (move-product MV02939.proved (move-product MV00697.proved (MV02939.proved)))))))

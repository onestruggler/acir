{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij23470156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; K2347 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00697 as MV00697
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02437 as MV02437
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K2347 • K0156 ≈ K0156 • K2347
proved = GL.•-cancelʳ {g = K2347 • K0156} {g' = K0156 • K2347} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00697.proved (MV02437.proved))) (trans (cong refl Base.proved) (move-product MV02437.proved (MV00697.proved))))

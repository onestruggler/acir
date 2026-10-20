{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1245 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00679 as MV00679
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01903 as MV01903
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K1245 ≈ K1245 • M0
proved = GL.•-cancelʳ {g = M0 • K1245} {g' = K1245 • M0} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01903.proved (MV00679.proved))) (trans (cong refl Base.proved) (move-product MV00679.proved (MV01903.proved))))

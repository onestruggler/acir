{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij10457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00672 as MV00672
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01950 as MV01950
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K0457 ≈ K0457 • M1
proved = GL.•-cancelʳ {g = M1 • K0457} {g' = K0457 • M1} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01950.proved (MV00672.proved))) (trans (cong refl Base.proved) (move-product MV00672.proved (MV01950.proved))))

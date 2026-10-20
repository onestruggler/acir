{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1236 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00677 as MV00677
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01901 as MV01901
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K1236 ≈ K1236 • M0
proved = GL.•-cancelʳ {g = M0 • K1236} {g' = K1236 • M0} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01901.proved (MV00677.proved))) (trans (cong refl Base.proved) (move-product MV00677.proved (MV01901.proved))))

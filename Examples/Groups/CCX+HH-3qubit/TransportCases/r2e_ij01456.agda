{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1456 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00691 as MV00691
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01915 as MV01915
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K1456 ≈ K1456 • M0
proved = GL.•-cancelʳ {g = M0 • K1456} {g' = K1456 • M0} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01915.proved (MV00691.proved))) (trans (cong refl Base.proved) (move-product MV00691.proved (MV01915.proved))))

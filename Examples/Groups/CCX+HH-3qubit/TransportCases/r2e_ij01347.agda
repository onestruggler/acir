{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1347 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00687 as MV00687
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01911 as MV01911
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K1347 ≈ K1347 • M0
proved = GL.•-cancelʳ {g = M0 • K1347} {g' = K1347 • M0} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01911.proved (MV00687.proved))) (trans (cong refl Base.proved) (move-product MV00687.proved (MV01911.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00680 as MV00680
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01904 as MV01904
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K1246 ≈ K1246 • M0
proved = GL.•-cancelʳ {g = M0 • K1246} {g' = K1246 • M0} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01904.proved (MV00680.proved))) (trans (cong refl Base.proved) (move-product MV00680.proved (MV01904.proved))))

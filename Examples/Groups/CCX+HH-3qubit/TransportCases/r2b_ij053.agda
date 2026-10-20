{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij053 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00753 as MV00753
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00754 as MV00754
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X05 • M3 ≈ M3 • X05
proved = GL.•-cancelʳ {g = X05 • M3} {g' = M3 • X05} {h = p (s2 • s1 • s0 • s4 • s3 • s2)}
  (trans (sym (move-product MV00753.proved (MV00754.proved))) (trans (cong refl Base.proved) (move-product MV00754.proved (MV00753.proved))))

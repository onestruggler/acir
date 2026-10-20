{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij054 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00755 as MV00755
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00756 as MV00756
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X05 • M4 ≈ M4 • X05
proved = GL.•-cancelʳ {g = X05 • M4} {g' = M4 • X05} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2)}
  (trans (sym (move-product MV00755.proved (MV00756.proved))) (trans (cong refl Base.proved) (move-product MV00756.proved (MV00755.proved))))

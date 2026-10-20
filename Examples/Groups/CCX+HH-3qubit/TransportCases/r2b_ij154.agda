{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij154 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00824 as MV00824
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00825 as MV00825
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X15 • M4 ≈ M4 • X15
proved = GL.•-cancelʳ {g = X15 • M4} {g' = M4 • X15} {h = p (s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00824.proved (MV00825.proved))) (trans (cong refl Base.proved) (move-product MV00825.proved (MV00824.proved))))

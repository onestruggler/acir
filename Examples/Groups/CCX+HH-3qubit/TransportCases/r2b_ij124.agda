{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00788 as MV00788
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00789 as MV00789
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X12 • M4 ≈ M4 • X12
proved = GL.•-cancelʳ {g = X12 • M4} {g' = M4 • X12} {h = p (s3 • s2 • s1 • s0 • s1 • s2)}
  (trans (sym (move-product MV00788.proved (MV00789.proved))) (trans (cong refl Base.proved) (move-product MV00789.proved (MV00788.proved))))

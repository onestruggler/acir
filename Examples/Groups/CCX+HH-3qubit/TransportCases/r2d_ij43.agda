{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij43 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00637 as MV00637
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01854 as MV01854
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M4 • M3 ≈ M3 • M4
proved = GL.•-cancelʳ {g = M4 • M3} {g' = M3 • M4} {h = p (s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00637.proved (MV01854.proved))) (trans (cong refl Base.proved) (move-product MV01854.proved (MV00637.proved))))

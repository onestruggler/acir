{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij14 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00000 as MV00000
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00028 as MV00028
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M1 • M4 ≈ M4 • M1
proved = GL.•-cancelʳ {g = M1 • M4} {g' = M4 • M1} {h = p (s0)}
  (trans (sym (move-product MV00000.proved (MV00028.proved))) (trans (cong refl Base.proved) (move-product MV00028.proved (MV00000.proved))))

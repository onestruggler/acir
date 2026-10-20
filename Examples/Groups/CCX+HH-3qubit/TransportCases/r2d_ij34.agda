{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij34 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00630 as MV00630
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01841 as MV01841
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M3 • M4 ≈ M4 • M3
proved = GL.•-cancelʳ {g = M3 • M4} {g' = M4 • M3} {h = p (s2 • s1 • s0)}
  (trans (sym (move-product MV00630.proved (MV01841.proved))) (trans (cong refl Base.proved) (move-product MV01841.proved (MV00630.proved))))

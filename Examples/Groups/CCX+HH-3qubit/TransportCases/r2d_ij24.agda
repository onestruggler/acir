{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij24 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00636 as MV00636
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01828 as MV01828
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M2 • M4 ≈ M4 • M2
proved = GL.•-cancelʳ {g = M2 • M4} {g' = M4 • M2} {h = p (s1 • s0)}
  (trans (sym (move-product MV00636.proved (MV01828.proved))) (trans (cong refl Base.proved) (move-product MV01828.proved (MV00636.proved))))

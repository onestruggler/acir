{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij012 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00636 as MV00636
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00709 as MV00709
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X01 • M2 ≈ M2 • X01
proved = GL.•-cancelʳ {g = X01 • M2} {g' = M2 • X01} {h = p (s1 • s0)}
  (trans (sym (move-product MV00709.proved (MV00636.proved))) (trans (cong refl Base.proved) (move-product MV00636.proved (MV00709.proved))))

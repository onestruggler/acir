{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij016 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00639 as MV00639
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00713 as MV00713
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X01 • M6 ≈ M6 • X01
proved = GL.•-cancelʳ {g = X01 • M6} {g' = M6 • X01} {h = p (s5 • s4 • s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00713.proved (MV00639.proved))) (trans (cong refl Base.proved) (move-product MV00639.proved (MV00713.proved))))

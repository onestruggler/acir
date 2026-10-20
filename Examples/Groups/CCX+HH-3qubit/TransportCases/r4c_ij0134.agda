{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; X14 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00645 as MV00645
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02572 as MV02572
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02967 as MV02967
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X34 • K0134 ≈ K0134 • X14
proved = GL.•-cancelʳ {g = X34 • K0134} {g' = K0134 • X14} {h = p (s2 • s3)}
  (trans (sym (move-product MV02967.proved (MV00645.proved))) (trans (cong refl Base.proved) (move-product MV00645.proved (MV02572.proved))))

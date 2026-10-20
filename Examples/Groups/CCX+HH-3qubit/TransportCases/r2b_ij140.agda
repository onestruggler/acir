{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij140 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00806 as MV00806
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00807 as MV00807
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X14 • M0 ≈ M0 • X14
proved = GL.•-cancelʳ {g = X14 • M0} {g' = M0 • X14} {h = p (s3 • s2)}
  (trans (sym (move-product MV00806.proved (MV00807.proved))) (trans (cong refl Base.proved) (move-product MV00807.proved (MV00806.proved))))

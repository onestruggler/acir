{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij143 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00810 as MV00810
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00811 as MV00811
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X14 • M3 ≈ M3 • X14
proved = GL.•-cancelʳ {g = X14 • M3} {g' = M3 • X14} {h = p (s2 • s1 • s0 • s1 • s3 • s2)}
  (trans (sym (move-product MV00810.proved (MV00811.proved))) (trans (cong refl Base.proved) (move-product MV00811.proved (MV00810.proved))))

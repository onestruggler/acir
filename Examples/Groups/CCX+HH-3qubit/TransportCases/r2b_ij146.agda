{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00814 as MV00814
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00815 as MV00815
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X14 • M6 ≈ M6 • X14
proved = GL.•-cancelʳ {g = X14 • M6} {g' = M6 • X14} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00814.proved (MV00815.proved))) (trans (cong refl Base.proved) (move-product MV00815.proved (MV00814.proved))))

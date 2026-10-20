{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij243 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00870 as MV00870
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00871 as MV00871
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X24 • M3 ≈ M3 • X24
proved = GL.•-cancelʳ {g = X24 • M3} {g' = M3 • X24} {h = p (s2 • s1 • s0 • s2 • s1 • s3 • s2)}
  (trans (sym (move-product MV00870.proved (MV00871.proved))) (trans (cong refl Base.proved) (move-product MV00871.proved (MV00870.proved))))

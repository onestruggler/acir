{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij341 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00916 as MV00916
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00917 as MV00917
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X34 • M1 ≈ M1 • X34
proved = GL.•-cancelʳ {g = X34 • M1} {g' = M1 • X34} {h = p (s0 • s2 • s1 • s3 • s2)}
  (trans (sym (move-product MV00916.proved (MV00917.proved))) (trans (cong refl Base.proved) (move-product MV00917.proved (MV00916.proved))))

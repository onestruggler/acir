{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00798 as MV00798
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00799 as MV00799
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X13 • M4 ≈ M4 • X13
proved = GL.•-cancelʳ {g = X13 • M4} {g' = M4 • X13} {h = p (s3 • s2 • s1 • s0 • s1 • s3 • s2)}
  (trans (sym (move-product MV00798.proved (MV00799.proved))) (trans (cong refl Base.proved) (move-product MV00799.proved (MV00798.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij162 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00832 as MV00832
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00833 as MV00833
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X16 • M2 ≈ M2 • X16
proved = GL.•-cancelʳ {g = X16 • M2} {g' = M2 • X16} {h = p (s1 • s0 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00832.proved (MV00833.proved))) (trans (cong refl Base.proved) (move-product MV00833.proved (MV00832.proved))))

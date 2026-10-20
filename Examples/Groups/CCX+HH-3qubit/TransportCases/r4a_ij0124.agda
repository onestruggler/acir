{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; M1 ; M4 ; X01 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00010 as MV00010
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00024 as MV00024
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00058 as MV00058
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as MV00113
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as MV00245
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X01 • K0124 ≈ K0124 • X14 • M1 • M4
proved = GL.•-cancelʳ {g = X01 • K0124} {g' = K0124 • X14 • M1 • M4} {h = p (s3)}
  (trans (sym (move-product MV00058.proved (MV00245.proved))) (trans (cong refl Base.proved) (move-product MV00245.proved (move-product MV00113.proved (move-product MV00010.proved (MV00024.proved))))))

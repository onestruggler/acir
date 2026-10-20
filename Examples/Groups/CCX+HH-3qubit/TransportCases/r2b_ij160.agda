{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij160 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00830 as MV00830
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00831 as MV00831
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X16 • M0 ≈ M0 • X16
proved = GL.•-cancelʳ {g = X16 • M0} {g' = M0 • X16} {h = p (s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00830.proved (MV00831.proved))) (trans (cong refl Base.proved) (move-product MV00831.proved (MV00830.proved))))

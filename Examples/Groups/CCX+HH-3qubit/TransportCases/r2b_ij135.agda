{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00800 as MV00800
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00801 as MV00801
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X13 • M5 ≈ M5 • X13
proved = GL.•-cancelʳ {g = X13 • M5} {g' = M5 • X13} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)}
  (trans (sym (move-product MV00800.proved (MV00801.proved))) (trans (cong refl Base.proved) (move-product MV00801.proved (MV00800.proved))))

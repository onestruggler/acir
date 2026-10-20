{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00802 as MV00802
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00803 as MV00803
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X13 • M6 ≈ M6 • X13
proved = GL.•-cancelʳ {g = X13 • M6} {g' = M6 • X13} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)}
  (trans (sym (move-product MV00802.proved (MV00803.proved))) (trans (cong refl Base.proved) (move-product MV00803.proved (MV00802.proved))))

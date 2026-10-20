{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00786 as MV00786
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00787 as MV00787
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X12 • M3 ≈ M3 • X12
proved = GL.•-cancelʳ {g = X12 • M3} {g' = M3 • X12} {h = p (s2 • s1 • s0 • s1 • s2)}
  (trans (sym (move-product MV00786.proved (MV00787.proved))) (trans (cong refl Base.proved) (move-product MV00787.proved (MV00786.proved))))

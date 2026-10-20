{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij132 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00796 as MV00796
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00797 as MV00797
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X13 • M2 ≈ M2 • X13
proved = GL.•-cancelʳ {g = X13 • M2} {g' = M2 • X13} {h = p (s1 • s0 • s1 • s2)}
  (trans (sym (move-product MV00796.proved (MV00797.proved))) (trans (cong refl Base.proved) (move-product MV00797.proved (MV00796.proved))))

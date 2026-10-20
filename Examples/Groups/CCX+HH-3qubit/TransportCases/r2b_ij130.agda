{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij130 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00002 as MV00002
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as MV00105
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X13 • M0 ≈ M0 • X13
proved = GL.•-cancelʳ {g = X13 • M0} {g' = M0 • X13} {h = p (s2)}
  (trans (sym (move-product MV00105.proved (MV00002.proved))) (trans (cong refl Base.proved) (move-product MV00002.proved (MV00105.proved))))

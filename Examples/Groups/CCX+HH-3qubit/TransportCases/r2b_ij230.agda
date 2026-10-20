{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij230 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00854 as MV00854
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00855 as MV00855
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X23 • M0 ≈ M0 • X23
proved = GL.•-cancelʳ {g = X23 • M0} {g' = M0 • X23} {h = p (s1 • s2)}
  (trans (sym (move-product MV00854.proved (MV00855.proved))) (trans (cong refl Base.proved) (move-product MV00855.proved (MV00854.proved))))

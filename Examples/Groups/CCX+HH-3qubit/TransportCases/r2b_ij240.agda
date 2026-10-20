{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij240 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00866 as MV00866
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00867 as MV00867
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X24 • M0 ≈ M0 • X24
proved = GL.•-cancelʳ {g = X24 • M0} {g' = M0 • X24} {h = p (s1 • s3 • s2)}
  (trans (sym (move-product MV00866.proved (MV00867.proved))) (trans (cong refl Base.proved) (move-product MV00867.proved (MV00866.proved))))

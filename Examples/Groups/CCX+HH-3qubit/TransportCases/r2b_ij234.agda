{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00858 as MV00858
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00859 as MV00859
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X23 • M4 ≈ M4 • X23
proved = GL.•-cancelʳ {g = X23 • M4} {g' = M4 • X23} {h = p (s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)}
  (trans (sym (move-product MV00858.proved (MV00859.proved))) (trans (cong refl Base.proved) (move-product MV00859.proved (MV00858.proved))))

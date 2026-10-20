{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij340 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00914 as MV00914
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00915 as MV00915
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X34 • M0 ≈ M0 • X34
proved = GL.•-cancelʳ {g = X34 • M0} {g' = M0 • X34} {h = p (s2 • s1 • s3 • s2)}
  (trans (sym (move-product MV00914.proved (MV00915.proved))) (trans (cong refl Base.proved) (move-product MV00915.proved (MV00914.proved))))

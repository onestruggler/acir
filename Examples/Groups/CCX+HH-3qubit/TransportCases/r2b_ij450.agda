{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij450 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00962 as MV00962
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00963 as MV00963
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X45 • M0 ≈ M0 • X45
proved = GL.•-cancelʳ {g = X45 • M0} {g' = M0 • X45} {h = p (s3 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00962.proved (MV00963.proved))) (trans (cong refl Base.proved) (move-product MV00963.proved (MV00962.proved))))

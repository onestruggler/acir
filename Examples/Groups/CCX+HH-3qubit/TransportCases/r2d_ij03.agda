{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij03 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00003 as MV00003
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as MV00031
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M0 • M3 ≈ M3 • M0
proved = GL.•-cancelʳ {g = M0 • M3} {g' = M3 • M0} {h = p (s3)}
  (trans (sym (move-product MV00003.proved (MV00031.proved))) (trans (cong refl Base.proved) (move-product MV00031.proved (MV00003.proved))))

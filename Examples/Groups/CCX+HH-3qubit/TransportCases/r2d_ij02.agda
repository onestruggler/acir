{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij02 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01803 as MV01803
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01804 as MV01804
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M0 • M2 ≈ M2 • M0
proved = GL.•-cancelʳ {g = M0 • M2} {g' = M2 • M0} {h = p (s2 • s3)}
  (trans (sym (move-product MV01803.proved (MV01804.proved))) (trans (cong refl Base.proved) (move-product MV01804.proved (MV01803.proved))))

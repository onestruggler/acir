{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij40 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01848 as MV01848
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01849 as MV01849
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M4 • M0 ≈ M0 • M4
proved = GL.•-cancelʳ {g = M4 • M0} {g' = M0 • M4} {h = p (s3 • s2 • s1 • s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV01848.proved (MV01849.proved))) (trans (cong refl Base.proved) (move-product MV01849.proved (MV01848.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij10 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01810 as MV01810
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01811 as MV01811
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M1 • M0 ≈ M0 • M1
proved = GL.•-cancelʳ {g = M1 • M0} {g' = M0 • M1} {h = p (s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV01810.proved (MV01811.proved))) (trans (cong refl Base.proved) (move-product MV01811.proved (MV01810.proved))))

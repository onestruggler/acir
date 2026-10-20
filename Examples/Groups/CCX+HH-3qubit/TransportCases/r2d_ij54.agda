{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij54 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01868 as MV01868
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01869 as MV01869
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M5 • M4 ≈ M4 • M5
proved = GL.•-cancelʳ {g = M5 • M4} {g' = M4 • M5} {h = p (s4 • s3 • s2 • s1 • s0 • s4)}
  (trans (sym (move-product MV01868.proved (MV01869.proved))) (trans (cong refl Base.proved) (move-product MV01869.proved (MV01868.proved))))

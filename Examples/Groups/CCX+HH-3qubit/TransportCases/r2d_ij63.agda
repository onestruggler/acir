{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij63 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00639 as MV00639
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01880 as MV01880
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M6 • M3 ≈ M3 • M6
proved = GL.•-cancelʳ {g = M6 • M3} {g' = M3 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00639.proved (MV01880.proved))) (trans (cong refl Base.proved) (move-product MV01880.proved (MV00639.proved))))

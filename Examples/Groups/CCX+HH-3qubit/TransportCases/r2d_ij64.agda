{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij64 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01881 as MV01881
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01882 as MV01882
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M6 • M4 ≈ M4 • M6
proved = GL.•-cancelʳ {g = M6 • M4} {g' = M4 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s4)}
  (trans (sym (move-product MV01881.proved (MV01882.proved))) (trans (cong refl Base.proved) (move-product MV01882.proved (MV01881.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij65 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01883 as MV01883
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01884 as MV01884
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M6 • M5 ≈ M5 • M6
proved = GL.•-cancelʳ {g = M6 • M5} {g' = M5 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4)}
  (trans (sym (move-product MV01883.proved (MV01884.proved))) (trans (cong refl Base.proved) (move-product MV01884.proved (MV01883.proved))))

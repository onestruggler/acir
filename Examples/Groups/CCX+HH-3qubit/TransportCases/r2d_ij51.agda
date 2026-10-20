{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij51 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01863 as MV01863
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01864 as MV01864
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M5 • M1 ≈ M1 • M5
proved = GL.•-cancelʳ {g = M5 • M1} {g' = M1 • M5} {h = p (s4 • s3 • s2 • s1 • s0 • s2 • s3)}
  (trans (sym (move-product MV01863.proved (MV01864.proved))) (trans (cong refl Base.proved) (move-product MV01864.proved (MV01863.proved))))

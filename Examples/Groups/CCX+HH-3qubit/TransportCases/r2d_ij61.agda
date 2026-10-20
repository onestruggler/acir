{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij61 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01876 as MV01876
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01877 as MV01877
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M6 • M1 ≈ M1 • M6
proved = GL.•-cancelʳ {g = M6 • M1} {g' = M1 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3)}
  (trans (sym (move-product MV01876.proved (MV01877.proved))) (trans (cong refl Base.proved) (move-product MV01877.proved (MV01876.proved))))

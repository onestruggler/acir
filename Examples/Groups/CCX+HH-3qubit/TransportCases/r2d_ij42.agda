{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij42 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01852 as MV01852
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01853 as MV01853
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M4 • M2 ≈ M2 • M4
proved = GL.•-cancelʳ {g = M4 • M2} {g' = M2 • M4} {h = p (s3 • s2 • s1 • s0 • s3)}
  (trans (sym (move-product MV01852.proved (MV01853.proved))) (trans (cong refl Base.proved) (move-product MV01853.proved (MV01852.proved))))

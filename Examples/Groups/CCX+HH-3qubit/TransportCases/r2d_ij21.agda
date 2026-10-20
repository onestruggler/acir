{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij21 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01824 as MV01824
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01825 as MV01825
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M2 • M1 ≈ M1 • M2
proved = GL.•-cancelʳ {g = M2 • M1} {g' = M1 • M2} {h = p (s1 • s0 • s2 • s3)}
  (trans (sym (move-product MV01824.proved (MV01825.proved))) (trans (cong refl Base.proved) (move-product MV01825.proved (MV01824.proved))))

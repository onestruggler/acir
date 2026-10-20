{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij13 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01814 as MV01814
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01815 as MV01815
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M1 • M3 ≈ M3 • M1
proved = GL.•-cancelʳ {g = M1 • M3} {g' = M3 • M1} {h = p (s0 • s3)}
  (trans (sym (move-product MV01814.proved (MV01815.proved))) (trans (cong refl Base.proved) (move-product MV01815.proved (MV01814.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij015 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00638 as MV00638
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00712 as MV00712
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X01 • M5 ≈ M5 • X01
proved = GL.•-cancelʳ {g = X01 • M5} {g' = M5 • X01} {h = p (s4 • s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00712.proved (MV00638.proved))) (trans (cong refl Base.proved) (move-product MV00638.proved (MV00712.proved))))

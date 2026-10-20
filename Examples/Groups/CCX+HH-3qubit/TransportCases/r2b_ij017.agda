{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij017 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00640 as MV00640
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00714 as MV00714
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X01 • M7 ≈ M7 • X01
proved = GL.•-cancelʳ {g = X01 • M7} {g' = M7 • X01} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00714.proved (MV00640.proved))) (trans (cong refl Base.proved) (move-product MV00640.proved (MV00714.proved))))

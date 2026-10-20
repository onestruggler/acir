{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij065 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00769 as MV00769
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00770 as MV00770
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X06 • M5 ≈ M5 • X06
proved = GL.•-cancelʳ {g = X06 • M5} {g' = M5 • X06} {h = p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00769.proved (MV00770.proved))) (trans (cong refl Base.proved) (move-product MV00770.proved (MV00769.proved))))

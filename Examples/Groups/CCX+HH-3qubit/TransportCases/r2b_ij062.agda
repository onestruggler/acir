{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij062 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00763 as MV00763
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00764 as MV00764
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X06 • M2 ≈ M2 • X06
proved = GL.•-cancelʳ {g = X06 • M2} {g' = M2 • X06} {h = p (s1 • s0 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00763.proved (MV00764.proved))) (trans (cong refl Base.proved) (move-product MV00764.proved (MV00763.proved))))

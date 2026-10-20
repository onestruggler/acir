{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij063 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00765 as MV00765
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00766 as MV00766
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X06 • M3 ≈ M3 • X06
proved = GL.•-cancelʳ {g = X06 • M3} {g' = M3 • X06} {h = p (s2 • s1 • s0 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00765.proved (MV00766.proved))) (trans (cong refl Base.proved) (move-product MV00766.proved (MV00765.proved))))

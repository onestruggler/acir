{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij064 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00767 as MV00767
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00768 as MV00768
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X06 • M4 ≈ M4 • X06
proved = GL.•-cancelʳ {g = X06 • M4} {g' = M4 • X06} {h = p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00767.proved (MV00768.proved))) (trans (cong refl Base.proved) (move-product MV00768.proved (MV00767.proved))))

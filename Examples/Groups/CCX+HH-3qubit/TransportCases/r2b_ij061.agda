{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij061 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00761 as MV00761
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00762 as MV00762
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X06 • M1 ≈ M1 • X06
proved = GL.•-cancelʳ {g = X06 • M1} {g' = M1 • X06} {h = p (s0 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00761.proved (MV00762.proved))) (trans (cong refl Base.proved) (move-product MV00762.proved (MV00761.proved))))

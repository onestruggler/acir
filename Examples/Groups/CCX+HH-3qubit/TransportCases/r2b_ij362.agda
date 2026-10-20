{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij362 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00942 as MV00942
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00943 as MV00943
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X36 • M2 ≈ M2 • X36
proved = GL.•-cancelʳ {g = X36 • M2} {g' = M2 • X36} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00942.proved (MV00943.proved))) (trans (cong refl Base.proved) (move-product MV00943.proved (MV00942.proved))))

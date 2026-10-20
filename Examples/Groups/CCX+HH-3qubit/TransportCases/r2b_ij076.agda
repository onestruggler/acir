{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij076 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X07 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00783 as MV00783
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00784 as MV00784
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X07 • M6 ≈ M6 • X07
proved = GL.•-cancelʳ {g = X07 • M6} {g' = M6 • X07} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00783.proved (MV00784.proved))) (trans (cong refl Base.proved) (move-product MV00784.proved (MV00783.proved))))

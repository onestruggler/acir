{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij374 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00956 as MV00956
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00957 as MV00957
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X37 • M4 ≈ M4 • X37
proved = GL.•-cancelʳ {g = X37 • M4} {g' = M4 • X37} {h = p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00956.proved (MV00957.proved))) (trans (cong refl Base.proved) (move-product MV00957.proved (MV00956.proved))))

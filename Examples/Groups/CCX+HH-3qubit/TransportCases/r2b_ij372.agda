{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij372 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00954 as MV00954
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00955 as MV00955
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X37 • M2 ≈ M2 • X37
proved = GL.•-cancelʳ {g = X37 • M2} {g' = M2 • X37} {h = p (s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00954.proved (MV00955.proved))) (trans (cong refl Base.proved) (move-product MV00955.proved (MV00954.proved))))

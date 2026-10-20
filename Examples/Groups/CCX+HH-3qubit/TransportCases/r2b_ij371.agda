{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij371 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00952 as MV00952
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00953 as MV00953
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X37 • M1 ≈ M1 • X37
proved = GL.•-cancelʳ {g = X37 • M1} {g' = M1 • X37} {h = p (s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00952.proved (MV00953.proved))) (trans (cong refl Base.proved) (move-product MV00953.proved (MV00952.proved))))

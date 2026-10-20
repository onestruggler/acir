{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij376 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00960 as MV00960
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00961 as MV00961
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X37 • M6 ≈ M6 • X37
proved = GL.•-cancelʳ {g = X37 • M6} {g' = M6 • X37} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00960.proved (MV00961.proved))) (trans (cong refl Base.proved) (move-product MV00961.proved (MV00960.proved))))

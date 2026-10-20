{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij375 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00958 as MV00958
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00959 as MV00959
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X37 • M5 ≈ M5 • X37
proved = GL.•-cancelʳ {g = X37 • M5} {g' = M5 • X37} {h = p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00958.proved (MV00959.proved))) (trans (cong refl Base.proved) (move-product MV00959.proved (MV00958.proved))))

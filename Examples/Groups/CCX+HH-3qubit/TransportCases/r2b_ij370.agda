{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij370 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00950 as MV00950
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00951 as MV00951
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X37 • M0 ≈ M0 • X37
proved = GL.•-cancelʳ {g = X37 • M0} {g' = M0 • X37} {h = p (s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00950.proved (MV00951.proved))) (trans (cong refl Base.proved) (move-product MV00951.proved (MV00950.proved))))

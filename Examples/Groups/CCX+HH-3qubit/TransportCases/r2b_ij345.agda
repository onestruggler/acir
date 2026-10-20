{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00920 as MV00920
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00921 as MV00921
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X34 • M5 ≈ M5 • X34
proved = GL.•-cancelʳ {g = X34 • M5} {g' = M5 • X34} {h = p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00920.proved (MV00921.proved))) (trans (cong refl Base.proved) (move-product MV00921.proved (MV00920.proved))))

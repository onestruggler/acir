{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij365 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00946 as MV00946
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00947 as MV00947
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X36 • M5 ≈ M5 • X36
proved = GL.•-cancelʳ {g = X36 • M5} {g' = M5 • X36} {h = p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00946.proved (MV00947.proved))) (trans (cong refl Base.proved) (move-product MV00947.proved (MV00946.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij075 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X07 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00781 as MV00781
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00782 as MV00782
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X07 • M5 ≈ M5 • X07
proved = GL.•-cancelʳ {g = X07 • M5} {g' = M5 • X07} {h = p (s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00781.proved (MV00782.proved))) (trans (cong refl Base.proved) (move-product MV00782.proved (MV00781.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij251 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00880 as MV00880
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00881 as MV00881
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X25 • M1 ≈ M1 • X25
proved = GL.•-cancelʳ {g = X25 • M1} {g' = M1 • X25} {h = p (s0 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00880.proved (MV00881.proved))) (trans (cong refl Base.proved) (move-product MV00881.proved (MV00880.proved))))

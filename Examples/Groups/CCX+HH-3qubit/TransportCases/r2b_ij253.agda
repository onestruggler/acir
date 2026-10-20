{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij253 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00882 as MV00882
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00883 as MV00883
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X25 • M3 ≈ M3 • X25
proved = GL.•-cancelʳ {g = X25 • M3} {g' = M3 • X25} {h = p (s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00882.proved (MV00883.proved))) (trans (cong refl Base.proved) (move-product MV00883.proved (MV00882.proved))))

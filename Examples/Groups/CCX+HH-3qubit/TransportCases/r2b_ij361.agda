{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij361 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00940 as MV00940
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00941 as MV00941
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X36 • M1 ≈ M1 • X36
proved = GL.•-cancelʳ {g = X36 • M1} {g' = M1 • X36} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00940.proved (MV00941.proved))) (trans (cong refl Base.proved) (move-product MV00941.proved (MV00940.proved))))

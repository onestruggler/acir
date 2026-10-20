{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00876 as MV00876
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00877 as MV00877
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X24 • M7 ≈ M7 • X24
proved = GL.•-cancelʳ {g = X24 • M7} {g' = M7 • X24} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00876.proved (MV00877.proved))) (trans (cong refl Base.proved) (move-product MV00877.proved (MV00876.proved))))

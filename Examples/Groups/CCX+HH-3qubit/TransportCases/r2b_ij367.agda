{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00948 as MV00948
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00949 as MV00949
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X36 • M7 ≈ M7 • X36
proved = GL.•-cancelʳ {g = X36 • M7} {g' = M7 • X36} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00948.proved (MV00949.proved))) (trans (cong refl Base.proved) (move-product MV00949.proved (MV00948.proved))))

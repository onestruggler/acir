{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij461 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00976 as MV00976
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00977 as MV00977
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X46 • M1 ≈ M1 • X46
proved = GL.•-cancelʳ {g = X46 • M1} {g' = M1 • X46} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00976.proved (MV00977.proved))) (trans (cong refl Base.proved) (move-product MV00977.proved (MV00976.proved))))

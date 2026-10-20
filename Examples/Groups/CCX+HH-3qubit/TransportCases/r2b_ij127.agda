{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00794 as MV00794
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00795 as MV00795
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X12 • M7 ≈ M7 • X12
proved = GL.•-cancelʳ {g = X12 • M7} {g' = M7 • X12} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2)}
  (trans (sym (move-product MV00794.proved (MV00795.proved))) (trans (cong refl Base.proved) (move-product MV00795.proved (MV00794.proved))))

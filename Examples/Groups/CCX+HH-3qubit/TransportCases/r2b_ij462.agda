{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij462 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00978 as MV00978
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00979 as MV00979
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X46 • M2 ≈ M2 • X46
proved = GL.•-cancelʳ {g = X46 • M2} {g' = M2 • X46} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00978.proved (MV00979.proved))) (trans (cong refl Base.proved) (move-product MV00979.proved (MV00978.proved))))

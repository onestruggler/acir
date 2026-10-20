{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij352 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00930 as MV00930
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00931 as MV00931
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X35 • M2 ≈ M2 • X35
proved = GL.•-cancelʳ {g = X35 • M2} {g' = M2 • X35} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00930.proved (MV00931.proved))) (trans (cong refl Base.proved) (move-product MV00931.proved (MV00930.proved))))

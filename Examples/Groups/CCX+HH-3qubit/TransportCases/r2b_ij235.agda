{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00860 as MV00860
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00861 as MV00861
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X23 • M5 ≈ M5 • X23
proved = GL.•-cancelʳ {g = X23 • M5} {g' = M5 • X23} {h = p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)}
  (trans (sym (move-product MV00860.proved (MV00861.proved))) (trans (cong refl Base.proved) (move-product MV00861.proved (MV00860.proved))))

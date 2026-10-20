{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij152 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00820 as MV00820
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00821 as MV00821
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X15 • M2 ≈ M2 • X15
proved = GL.•-cancelʳ {g = X15 • M2} {g' = M2 • X15} {h = p (s1 • s0 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00820.proved (MV00821.proved))) (trans (cong refl Base.proved) (move-product MV00821.proved (MV00820.proved))))

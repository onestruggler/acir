{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00826 as MV00826
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00827 as MV00827
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X15 • M6 ≈ M6 • X15
proved = GL.•-cancelʳ {g = X15 • M6} {g' = M6 • X15} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00826.proved (MV00827.proved))) (trans (cong refl Base.proved) (move-product MV00827.proved (MV00826.proved))))

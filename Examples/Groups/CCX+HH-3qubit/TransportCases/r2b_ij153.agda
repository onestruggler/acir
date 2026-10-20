{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij153 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00822 as MV00822
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00823 as MV00823
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X15 • M3 ≈ M3 • X15
proved = GL.•-cancelʳ {g = X15 • M3} {g' = M3 • X15} {h = p (s2 • s1 • s0 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00822.proved (MV00823.proved))) (trans (cong refl Base.proved) (move-product MV00823.proved (MV00822.proved))))

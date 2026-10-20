{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij056 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00757 as MV00757
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00758 as MV00758
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X05 • M6 ≈ M6 • X05
proved = GL.•-cancelʳ {g = X05 • M6} {g' = M6 • X05} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00757.proved (MV00758.proved))) (trans (cong refl Base.proved) (move-product MV00758.proved (MV00757.proved))))

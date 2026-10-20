{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as MV00031
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as MV00245
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0124 ≈ K0124 • M3
proved = GL.•-cancelʳ {g = M3 • K0124} {g' = K0124 • M3} {h = p (s3)}
  (trans (sym (move-product MV00031.proved (MV00245.proved))) (trans (cong refl Base.proved) (move-product MV00245.proved (MV00031.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij051 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00749 as MV00749
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00750 as MV00750
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X05 • M1 ≈ M1 • X05
proved = GL.•-cancelʳ {g = X05 • M1} {g' = M1 • X05} {h = p (s0 • s4 • s3 • s2)}
  (trans (sym (move-product MV00749.proved (MV00750.proved))) (trans (cong refl Base.proved) (move-product MV00750.proved (MV00749.proved))))

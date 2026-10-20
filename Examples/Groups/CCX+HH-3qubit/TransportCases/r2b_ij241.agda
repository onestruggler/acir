{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij241 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00868 as MV00868
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00869 as MV00869
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X24 • M1 ≈ M1 • X24
proved = GL.•-cancelʳ {g = X24 • M1} {g' = M1 • X24} {h = p (s0 • s1 • s3 • s2)}
  (trans (sym (move-product MV00868.proved (MV00869.proved))) (trans (cong refl Base.proved) (move-product MV00869.proved (MV00868.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij014 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00637 as MV00637
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00711 as MV00711
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X01 • M4 ≈ M4 • X01
proved = GL.•-cancelʳ {g = X01 • M4} {g' = M4 • X01} {h = p (s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00711.proved (MV00637.proved))) (trans (cong refl Base.proved) (move-product MV00637.proved (MV00711.proved))))

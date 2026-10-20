{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij45 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01855 as MV01855
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01856 as MV01856
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M4 • M5 ≈ M5 • M4
proved = GL.•-cancelʳ {g = M4 • M5} {g' = M5 • M4} {h = p (s3 • s2 • s1 • s0 • s4)}
  (trans (sym (move-product MV01855.proved (MV01856.proved))) (trans (cong refl Base.proved) (move-product MV01856.proved (MV01855.proved))))

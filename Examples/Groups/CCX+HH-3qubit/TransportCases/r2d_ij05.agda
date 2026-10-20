{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij05 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00004 as MV00004
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as MV00032
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M0 • M5 ≈ M5 • M0
proved = GL.•-cancelʳ {g = M0 • M5} {g' = M5 • M0} {h = p (s4)}
  (trans (sym (move-product MV00004.proved (MV00032.proved))) (trans (cong refl Base.proved) (move-product MV00032.proved (MV00004.proved))))

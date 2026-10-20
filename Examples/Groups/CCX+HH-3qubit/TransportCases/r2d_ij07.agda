{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij07 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01808 as MV01808
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01809 as MV01809
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M0 • M7 ≈ M7 • M0
proved = GL.•-cancelʳ {g = M0 • M7} {g' = M7 • M0} {h = p (s6 • s5 • s4)}
  (trans (sym (move-product MV01808.proved (MV01809.proved))) (trans (cong refl Base.proved) (move-product MV01809.proved (MV01808.proved))))

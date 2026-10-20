{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij25 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01829 as MV01829
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01830 as MV01830
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M2 • M5 ≈ M5 • M2
proved = GL.•-cancelʳ {g = M2 • M5} {g' = M5 • M2} {h = p (s1 • s0 • s4)}
  (trans (sym (move-product MV01829.proved (MV01830.proved))) (trans (cong refl Base.proved) (move-product MV01830.proved (MV01829.proved))))

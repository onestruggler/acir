{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij36 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01844 as MV01844
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01845 as MV01845
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M3 • M6 ≈ M6 • M3
proved = GL.•-cancelʳ {g = M3 • M6} {g' = M6 • M3} {h = p (s2 • s1 • s0 • s5 • s4)}
  (trans (sym (move-product MV01844.proved (MV01845.proved))) (trans (cong refl Base.proved) (move-product MV01845.proved (MV01844.proved))))

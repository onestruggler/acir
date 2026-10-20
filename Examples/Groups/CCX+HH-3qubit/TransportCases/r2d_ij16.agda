{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij16 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01818 as MV01818
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01819 as MV01819
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M1 • M6 ≈ M6 • M1
proved = GL.•-cancelʳ {g = M1 • M6} {g' = M6 • M1} {h = p (s0 • s5 • s4)}
  (trans (sym (move-product MV01818.proved (MV01819.proved))) (trans (cong refl Base.proved) (move-product MV01819.proved (MV01818.proved))))

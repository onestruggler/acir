{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij35 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01842 as MV01842
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01843 as MV01843
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M3 • M5 ≈ M5 • M3
proved = GL.•-cancelʳ {g = M3 • M5} {g' = M5 • M3} {h = p (s2 • s1 • s0 • s4)}
  (trans (sym (move-product MV01842.proved (MV01843.proved))) (trans (cong refl Base.proved) (move-product MV01843.proved (MV01842.proved))))

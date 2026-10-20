{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij37 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01846 as MV01846
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01847 as MV01847
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M3 • M7 ≈ M7 • M3
proved = GL.•-cancelʳ {g = M3 • M7} {g' = M7 • M3} {h = p (s2 • s1 • s0 • s6 • s5 • s4)}
  (trans (sym (move-product MV01846.proved (MV01847.proved))) (trans (cong refl Base.proved) (move-product MV01847.proved (MV01846.proved))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij27 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01833 as MV01833
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01834 as MV01834
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M2 • M7 ≈ M7 • M2
proved = GL.•-cancelʳ {g = M2 • M7} {g' = M7 • M2} {h = p (s1 • s0 • s6 • s5 • s4)}
  (trans (sym (move-product MV01833.proved (MV01834.proved))) (trans (cong refl Base.proved) (move-product MV01834.proved (MV01833.proved))))

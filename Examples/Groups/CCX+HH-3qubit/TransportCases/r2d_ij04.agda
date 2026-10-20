{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij04 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00635 as MV00635
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01805 as MV01805
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M0 • M4 ≈ M4 • M0
proved = GL.•-cancelʳ {g = M0 • M4} {g' = M4 • M0} {h = p (ε)}
  (trans (sym (move-product MV00635.proved (MV01805.proved))) (trans (cong refl Base.proved) (move-product MV01805.proved (MV00635.proved))))

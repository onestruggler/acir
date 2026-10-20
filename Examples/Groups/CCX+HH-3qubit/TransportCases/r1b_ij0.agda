{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij0 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00635 as MV00635
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as Base

proved : M0 • M0 ≈ ε
proved = GL.•-cancelʳ {g = M0 • M0} {g' = ε} {h = p (ε)}
  (trans (sym (move-product MV00635.proved (MV00635.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))

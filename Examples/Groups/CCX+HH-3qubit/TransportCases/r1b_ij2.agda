{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij2 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00636 as MV00636
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as Base

proved : M2 • M2 ≈ ε
proved = GL.•-cancelʳ {g = M2 • M2} {g' = ε} {h = p (s1 • s0)}
  (trans (sym (move-product MV00636.proved (MV00636.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))

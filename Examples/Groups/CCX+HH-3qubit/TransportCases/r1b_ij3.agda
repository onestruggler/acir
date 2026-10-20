{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij3 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00630 as MV00630
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as Base

proved : M3 • M3 ≈ ε
proved = GL.•-cancelʳ {g = M3 • M3} {g' = ε} {h = p (s2 • s1 • s0)}
  (trans (sym (move-product MV00630.proved (MV00630.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))

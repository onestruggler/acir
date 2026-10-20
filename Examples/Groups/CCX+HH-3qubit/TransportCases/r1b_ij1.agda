{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij1 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00000 as MV00000
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as Base

proved : M1 • M1 ≈ ε
proved = GL.•-cancelʳ {g = M1 • M1} {g' = ε} {h = p (s0)}
  (trans (sym (move-product MV00000.proved (MV00000.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))

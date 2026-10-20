{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij5 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00638 as MV00638
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as Base

proved : M5 • M5 ≈ ε
proved = GL.•-cancelʳ {g = M5 • M5} {g' = ε} {h = p (s4 • s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00638.proved (MV00638.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))

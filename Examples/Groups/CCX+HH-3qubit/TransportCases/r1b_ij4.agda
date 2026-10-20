{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij4 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00637 as MV00637
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as Base

proved : M4 • M4 ≈ ε
proved = GL.•-cancelʳ {g = M4 • M4} {g' = ε} {h = p (s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00637.proved (MV00637.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij6 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00639 as MV00639
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as Base

proved : M6 • M6 ≈ ε
proved = GL.•-cancelʳ {g = M6 • M6} {g' = ε} {h = p (s5 • s4 • s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00639.proved (MV00639.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))

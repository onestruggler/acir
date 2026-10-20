{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij7 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00640 as MV00640
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as Base

proved : M7 • M7 ≈ ε
proved = GL.•-cancelʳ {g = M7 • M7} {g' = ε} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00640.proved (MV00640.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))

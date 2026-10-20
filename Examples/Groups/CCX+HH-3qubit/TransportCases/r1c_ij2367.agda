{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij2367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2367 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00700 as MV00700
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K2367 • K2367 ≈ ε
proved = GL.•-cancelʳ {g = K2367 • K2367} {g' = ε} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00700.proved (MV00700.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))

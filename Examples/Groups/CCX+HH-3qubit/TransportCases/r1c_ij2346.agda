{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij2346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2346 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00696 as MV00696
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K2346 • K2346 ≈ ε
proved = GL.•-cancelʳ {g = K2346 • K2346} {g' = ε} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00696.proved (MV00696.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
